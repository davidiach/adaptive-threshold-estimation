"""Reject weakened corollaries, altered models, proof escapes and incomplete audits."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify_closed_quantile as audit
import verify_blind_upper_components as shared


class ClosedQuantileAuditTests(unittest.TestCase):
    def test_complete_registry(self):
        paths,ordered,roots=audit.validate_sources()
        self.assertEqual(len(paths),2)
        self.assertEqual(len(roots),2)
        self.assertEqual([p for p in ordered if p in paths],paths)
        self.assertTrue(set(audit.EXACT_TARGETS)<=roots)

    def test_weakened_or_missing_exact_target_rejected(self):
        name=next(iter(audit.EXACT_TARGETS))
        for targets in ({},{name:'True'}):
            with self.subTest(targets=targets),patch.object(audit,'EXACT_TARGETS',targets):
                with self.assertRaisesRegex(ValueError,'exact closed-quantile target'):
                    audit.validate_sources()

    def test_changed_specification_or_record_rejected(self):
        real_sha=audit.sha
        with patch.object(audit,'sha',side_effect=lambda p:'0'*64 if p==audit.SOURCE/'Specification.lean' else real_sha(p)):
            with self.assertRaisesRegex(ValueError,'specification changed'):
                audit.validate_sources()
        record=json.loads(audit.FREEZE.read_text(encoding='utf-8'))
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'freeze.json'
            for changes,message in (({'source_sha256':{}},'specification changed'),
                                    ({'targets':{}},'exact closed-quantile target')):
                p.write_text(json.dumps({**record,**changes}),encoding='utf-8')
                with self.subTest(changes=changes),patch.object(audit,'FREEZE',p):
                    with self.assertRaisesRegex(ValueError,message):
                        audit.validate_sources()

    def test_changed_risk_or_quantile_model_rejected(self):
        real_sha=shared.sha
        for name in ('lean/ThresholdHC/RareAboveTwo/Model.lean',
                     'lean/ThresholdHC/EntropyTailQuantile/Model.lean'):
            with self.subTest(name=name),patch.object(shared,'sha',side_effect=
                    lambda p:'0'*64 if p==audit.ROOT/name else real_sha(p)):
                with self.assertRaisesRegex(ValueError,'dependency changed'):
                    audit.validate_sources()

    def test_missing_duplicate_or_unregistered_module_rejected(self):
        for modules in (audit.MODULES[:-1],audit.MODULES+audit.MODULES[:1]):
            with self.subTest(modules=modules),patch.object(audit,'MODULES',modules):
                with self.assertRaisesRegex(ValueError,'unregistered'):
                    audit.validate_sources()
        real_rglob=Path.rglob
        def extra(path,pattern):
            found=list(real_rglob(path,pattern))
            return found+[audit.SOURCE/'Hidden.lean'] if path==audit.SOURCE else found
        with patch.object(Path,'rglob',extra):
            with self.assertRaisesRegex(ValueError,'unregistered'):
                audit.validate_sources()

    def test_missing_proof_rejected(self):
        real_read=Path.read_text
        def missing(path,*args,**kwargs):
            text=real_read(path,*args,**kwargs)
            return text.replace('theorem closed_quantile_law','theorem unrelated') if path==audit.SOURCE/'Full.lean' else text
        with patch.object(Path,'read_text',missing):
            with self.assertRaisesRegex(ValueError,'missing declaration root'):
                audit.validate_sources()

    def test_registered_and_imported_proof_escapes_rejected(self):
        real_read=Path.read_text
        for target in (audit.SOURCE/'Full.lean',audit.LEAN/'ThresholdHC/EntropyTailLower/CertificateLower.lean'):
            def planted(path,*args,**kwargs):
                text=real_read(path,*args,**kwargs)
                return text+'\nrun_cmd pure ()\n' if path==target else text
            with self.subTest(target=target),patch.object(Path,'read_text',planted):
                with self.assertRaisesRegex(ValueError,'Forbidden proof escape'):
                    audit.validate_sources()

    def test_cached_mode_uses_shared_dependency_guards(self):
        import verify_entropy_tail as canonical
        for name in ('cached_artifact_hashes','check_dependencies','native_commands',
                     'validate_stability','write_audit_source'):
            with self.subTest(name=name):
                self.assertIs(getattr(audit,name),getattr(canonical,name))
        paths,ordered,_=audit.validate_sources()
        self.assertEqual(canonical.dependency_command('lake',paths,False),
                         ['lake','build','--no-build','ThresholdHC.EntropyTail.Law',
                          'ThresholdHC.EntropyTailQuantile.Model'])

    def test_build_dependencies_requires_cached_mode(self):
        with patch('sys.argv',['verify_closed_quantile.py','--build-dependencies']), \
                patch('sys.stderr'),self.assertRaises(SystemExit) as raised:
            audit.main()
        self.assertEqual(raised.exception.code,2)

    def test_incomplete_unsafe_or_failed_reports_rejected(self):
        roots={audit.PREFIX+'ClosedQuantileLawStatement',audit.PREFIX+'closed_quantile_law'}
        lines=[f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in sorted(roots)]
        report='\n'.join(lines)
        self.assertEqual(set(audit.validate_reports(report,0,roots)),roots)
        for changed in (lines[0],report+'\n'+lines[0],report.replace('Quot.sound','sorryAx')):
            with self.subTest(changed=changed),self.assertRaises(ValueError):
                audit.validate_reports(changed,0,roots)
        with self.assertRaises(ValueError):
            audit.validate_reports(report,1,roots)


if __name__=='__main__':
    unittest.main()
