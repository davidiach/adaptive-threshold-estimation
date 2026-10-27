"""Package verified paper proofs; preserve inherited source bytes separately."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
items=[]
for source,target in [('inherited/construction.tex','inherited/construction-body.tex'),
                      ('upper/proof.tex','upper/proof-body.tex')]:
    text=(HERE/source).read_text(encoding='utf-8')
    body=text.split(r'\begin{document}',1)[1].rsplit(r'\end{document}',1)[0]
    body=body.replace(r'\maketitle','').replace(r'\appendix','% Appendix numbering supplied by the wrapper.')
    def break_code(match):
        value=match.group(1)
        if '/' in value:value=value.replace('/',r'/\allowbreak{}')
        elif len(value)>40:value=r'\allowbreak{}'.join(value[i:i+8] for i in range(0,len(value),8))
        return r'\texttt{'+value+'}'
    body=re.sub(r'\\texttt\{([^{}]+)\}',break_code,body)
    body=body.replace(r'\begin{center}\small\texttt{0e8b9eaf\allowbreak{}762b3b09\allowbreak{}fa0d92ce\allowbreak{}1a036c2c\allowbreak{}eea8c12d\allowbreak{}00a5eea8\allowbreak{}286b852f\allowbreak{}36a81536}\end{center}',
                      r'\begin{center}\small\texttt{0e8b9eaf762b3b09fa0d92ce1a036c2c}\\\texttt{eea8c12d00a5eea8286b852f36a81536}\end{center}')
    body=body.replace(r'\texttt{a8a8dc49115aabdd1fba8d53d3390eb0a5eee864}',r'\par\noindent\texttt{a8a8dc49115aabdd1fba8d53d3390eb0a5eee864}')
    (HERE/target).write_text('% Generated packaging derivative; source remains byte-preserved.\n'+body,encoding='utf-8')
    items.append(dict(source=source,source_sha256=hashlib.sha256((HERE/source).read_bytes()).hexdigest(),
                      target=target,target_sha256=hashlib.sha256((HERE/target).read_bytes()).hexdigest()))
(HERE/'NOTE_ASSEMBLY.json').write_text(json.dumps(dict(transform='extract document body; remove maketitle and appendix commands; permit line breaks in texttt paths and long hashes',files=items),indent=2)+'\n')
