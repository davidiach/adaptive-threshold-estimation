"""Package source proofs, without editing their mathematical content."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
records=[]
for name,targetname in [('proof.tex','proof-body.tex'),('FINITE_APPROXIMATION.tex','approximation-body.tex')]:
    source=HERE/'upper'/name
    s=source.read_text(encoding='utf-8')
    body=s.split(r'\begin{document}',1)[1].rsplit(r'\end{document}',1)[0].replace(r'\maketitle','')
    target=HERE/'upper'/targetname;target.write_text(body,encoding='utf-8')
    records.append(dict(source='upper/'+name,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),target='upper/'+targetname,target_sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
source=HERE/'lower/full_class.tex';target=HERE/'lower/full_class-body.tex'
body=source.read_text(encoding='utf-8').replace(r'\texttt{full\_class\_certificate.json}',r'\linebreak\texttt{full\_class\_certificate.json}')
target.write_text(body,encoding='utf-8')
records.append(dict(source='lower/full_class.tex',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),target='lower/full_class-body.tex',target_sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
(HERE/'NOTE_ASSEMBLY.json').write_text(json.dumps(dict(files=records,transformation='Extract standalone document bodies; remove maketitle; allow one line break before a certificate filename. Mathematics unchanged.'),indent=2)+'\n')
