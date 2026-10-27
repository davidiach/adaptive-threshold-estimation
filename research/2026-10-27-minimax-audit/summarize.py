from pathlib import Path
import csv,json,sys,math
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
from reportlab.graphics.shapes import Drawing,Line,Circle,String
from reportlab.graphics import renderPDF,renderSVG
from reportlab.lib.colors import HexColor

def main():
    data=json.loads((HERE/'BENCHMARK_RESULTS.json').read_text());assert data['complete']
    fields=['model','budget','method','theta','rho','epsilon','rmse_raw','rmse_clipped','bias_raw','bias_clipped','variance_raw','variance_clipped','miss_raw','miss_clipped','mean_work','work_p95','mean_outer_draws','seconds']
    with (HERE/'BENCHMARK_SUMMARY.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader()
        for r in data['rows']:
            o={k:r[k] for k in ['model','budget','method','theta','rho','epsilon','mean_work','mean_outer_draws','seconds']}
            for status in ['raw','clipped']:
                for name in ['rmse','bias','variance']:o[name+'_'+status]=r[status][name]
                o['miss_'+status]=r[status]['miss_probability']
            o['work_p95']=r['work_quantiles']['0.95'];writer.writerow(o)
    models=[m['name'] for m in json.loads((HERE/'PREREGISTRATION.json').read_text())['models']]
    fig=Drawing(720,320)
    colors=['#527a9e','#928b80','#c3533d']
    names=['GHA sampling rule, altered driver','Symmetric telescope','Asymmetric candidate']
    methods=['gha_calibrated_single_level','direct_symmetric','direct_asymmetric']
    xpos=lambda i:65+91*i
    ypos=lambda y:62+200*(math.log10(y)+2.5)/2.5
    for tick in [.005,.01,.02,.05,.1,.2,.5,1.]:
        y=ypos(tick);fig.add(Line(50,y,690,y,strokeColor=HexColor('#dddddd'),strokeWidth=.4))
        fig.add(String(44,y-3,str(tick),fontSize=8,textAnchor='end'))
    fig.add(String(52,306,'New locked suite: 128 replications per cell, nominal expected budget 16,384',fontSize=10))
    fig.add(String(8,150,'RMS error',fontSize=8,angle=90))
    for mi,(method,name) in enumerate(zip(methods,names)):
        rows=[next(r for r in data['rows'] if r['model']==model and r['budget']==16384 and r['method']==method) for model in models]
        color=HexColor(colors[mi]);fig.add(Circle(55+mi*220,286,3,fillColor=color,strokeColor=color))
        fig.add(String(63+mi*220,283,name,fontSize=8))
        for i,r in enumerate(rows):
            x=xpos(i)+(mi-1)*11;y=ypos(r['clipped']['rmse']);lo,hi=map(ypos,r['clipped']['descriptive_rmse_interval'])
            fig.add(Line(x,lo,x,hi,strokeColor=color));fig.add(Line(x-3,lo,x+3,lo,strokeColor=color));fig.add(Line(x-3,hi,x+3,hi,strokeColor=color));fig.add(Circle(x,y,3,fillColor=color,strokeColor=color))
    for i in range(6):fig.add(Line(xpos(i),ypos(data['trivial'][i]['zero_rmse']),xpos(i+1),ypos(data['trivial'][i+1]['zero_rmse']),strokeColor=HexColor('#777777'),strokeDashArray=[4,3]))
    labels=['GHA|0.025','GHA|0.005','Fixed|gap','Mixed|scales','Near-negative|population','Uniform-mean|Gaussian','Deterministic|endpoint']
    for i,label in enumerate(labels):
        for j,line in enumerate(label.split('|')):fig.add(String(xpos(i),44-11*j,line,fontSize=8,textAnchor='middle'))
    fig.add(String(50,10,'Dashed grey: constant zero. GHA uses an altered single-level driver. Intervals are descriptive.',fontSize=8))
    (HERE/'figures').mkdir(exist_ok=True);renderPDF.drawToFile(fig,str(HERE/'figures/benchmark.pdf'));renderSVG.drawToFile(fig,str(HERE/'figures/benchmark.svg'))
    print(json.dumps(dict(total_work=data['total_work'],seconds=data['seconds'],cells=len(data['rows']),runs=len(data['rows'])*128,
        asymmetric_better_than_symmetric=sum(next(r for r in data['rows'] if r['model']==m and r['budget']==b and r['method']=='direct_asymmetric')['clipped']['rmse'] < next(r for r in data['rows'] if r['model']==m and r['budget']==b and r['method']=='direct_symmetric')['clipped']['rmse'] for m in models for b in [4096,16384]))))

if __name__=='__main__':main()
