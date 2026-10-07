"""Finite affine codebook. Pure array operations; no model or activation access."""
import hashlib,json
from pathlib import Path
import numpy as np

FORMAT='finite_affine_v1'
BASE_SEED=2026100416

class QualityFailure(ValueError):
    """A failed identity with its measured operands; never a passing row."""
    def __init__(self, identity, operands, scale=None, tolerance=None):
        super().__init__(identity)
        self.evidence={'identity':identity,'operands':operands,'scale':scale,'tolerance':tolerance,'quality_pass':False}
        self.partial_result=None

def require(condition,identity,operands,scale=None,tolerance=None):
    if not condition:raise QualityFailure(identity,operands,scale,tolerance)


def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda:f.read(8*1024*1024),b''):h.update(chunk)
    return h.hexdigest()

def derive_seed(model,module):
    tag=f'c6-finite-v1|{model}|{module}|{BASE_SEED}'
    return int.from_bytes(hashlib.sha256(tag.encode('utf-8')).digest()[:8],'little')

def scale(w):
    return np.max(np.abs(w),axis=1)

def quantize(target,m,bits,seed=None,packet_path=None,extra=None):
    """Save/read the selected representation, then decode before measuring loss."""
    if bits not in (2,3,4):raise ValueError('undeclared bit count')
    target=np.asarray(target,dtype=np.float64);m=np.asarray(m,dtype=np.float64)
    if target.ndim!=2 or m.shape!=(target.shape[0],):raise ValueError('shape')
    if not np.isfinite(target).all() or not np.isfinite(m).all() or np.any(m<0):raise ValueError('finite input/range')
    zero=m==0
    if np.any(target[zero]!=0):raise ValueError('nonzero target with zero original row range')
    k=2**bits;delta=2*m/(k-1)
    u=np.zeros(target.shape,dtype=np.float64)
    if seed is not None:
        u=(np.random.Generator(np.random.PCG64(seed)).random(target.shape)-.5)*delta[:,None]
    normalized=np.divide(target+u,m[:,None],out=np.zeros_like(target),where=~zero[:,None])
    indices=np.clip(np.rint((normalized+1)*(k-1)/2),0,k-1).astype(np.uint8)
    indices[zero]=0
    metadata={'format':FORMAT,'shape':list(target.shape),'bits':bits,'seed':seed,
              'rng':'PCG64','numpy_version':np.__version__,'mode':'deterministic' if seed is None else 'subtractive_dither',
              'dtype':'float64','extra':extra or {}}
    before=decode_arrays(indices,m,metadata)
    if packet_path is not None:
        path=Path(packet_path);path.parent.mkdir(parents=True,exist_ok=True)
        if path.exists():raise FileExistsError(path)
        np.savez_compressed(path,indices=indices,m=m,metadata=np.array(json.dumps(metadata,sort_keys=True)))
        after,readmeta=decode_packet(path)
        if readmeta!=metadata or not np.array_equal(before,after):raise ValueError('packet round-trip mismatch')
        return after,{'path':str(path),'sha256':digest(path),'bytes':path.stat().st_size,'metadata':metadata}
    return before,None

def decode_arrays(indices,m,metadata):
    k=2**metadata['bits'];shape=tuple(metadata['shape'])
    if metadata['format']!=FORMAT or metadata['dtype']!='float64':raise ValueError('format')
    if metadata['rng']!='PCG64' or metadata['numpy_version']!=np.__version__:raise ValueError('RNG/environment mismatch')
    if indices.dtype!=np.uint8 or indices.shape!=shape or m.dtype!=np.float64 or m.shape!=(shape[0],):raise ValueError('saved shape/dtype')
    if not np.isfinite(m).all() or np.any(m<0) or np.any(indices>=k):raise ValueError('saved scale/code')
    q=(2*(indices.astype(np.float64)/(k-1))-1)*m[:,None]
    if metadata['seed'] is not None:
        u=(np.random.Generator(np.random.PCG64(int(metadata['seed']))).random(shape)-.5)*(2*m/(k-1))[:,None]
        q=q-u
    if not np.isfinite(q).all():raise FloatingPointError('decoded nonfinite')
    return q

def decode_packet(path):
    with np.load(path,allow_pickle=False) as p:
        if set(p.files)!={'indices','m','metadata'}:raise ValueError('packet fields')
        meta=json.loads(str(p['metadata']))
        return decode_arrays(p['indices'],p['m'],meta),meta

def ratio(numerator,denominator):
    if not np.isfinite([numerator,denominator]).all() or min(numerator,denominator)<0:raise FloatingPointError('invalid energy')
    if denominator==0:
        return {'value':None,'status':'infinite' if numerator>0 else 'both_zero_undefined'}
    value=float(numerator/denominator)
    if not np.isfinite(value):raise FloatingPointError('ratio overflow')
    return {'value':value,'status':'finite'}

def evaluate(w,c,alpha,bits,seed,packet_dir=None,extra=None,output_context=None):
    w=np.asarray(w,dtype=np.float64);c=np.asarray(c,dtype=np.float64)
    if w.shape!=c.shape or w.ndim!=2 or not min(w.shape):raise ValueError('W/C shape')
    if not np.isfinite(w).all() or not np.isfinite(c).all():raise ValueError('nonfinite W/C')
    m=scale(w);zero=m==0
    if np.any(c[zero]!=0):raise ValueError('zero W row requires exactly zero C row')
    target=w+alpha*c
    if not np.isfinite(target).all():raise FloatingPointError('target overflow')
    overload=target-np.clip(target,-m[:,None],m[:,None])
    count=int(np.count_nonzero((target < -m[:,None])|(target > m[:,None])))
    delta=2*m/(2**bits-1)
    paths=[None,None] if packet_dir is None else [Path(packet_dir)/'deterministic.npz',Path(packet_dir)/'subtractive_dither.npz']
    det,pdet=quantize(target,m,bits,None,paths[0],extra)
    sub,psub=quantize(target,m,bits,seed,paths[1],extra)
    de=float(np.mean(np.square(det-target)));se=float(np.mean(np.square(sub-target)))
    overload_energy=float(np.mean(np.square(overload)));variance=float(np.mean(np.square(delta)/12))
    expected=variance+overload_energy
    if not np.isfinite([de,se,expected,overload_energy,variance]).all():raise FloatingPointError('energy overflow')
    tol=1e-12*max(expected,de,1e-30)
    require(expected+tol>=de/3,'analytic lower-bound guard',{'expected':expected,'deterministic':de,'lower_bound':de/3},max(expected,de,1e-30),1e-12)
    result={'weights':int(w.size),'zero_rows':int(np.count_nonzero(zero)),
            'zero_row_entries':int(np.count_nonzero(zero))*w.shape[1],
            'overload_count':count,'overload_fraction':count/w.size,
            'max_excess':float(np.max(np.abs(overload))),
            'overload_mean_squared':overload_energy,'dither_variance_mean':variance,
            'deterministic_mse':de,'expected_dither_mse':expected,'realized_dither_mse':se,
            'expected_ratio':ratio(expected,de),'realized_ratio':ratio(se,de),
            'quality_pass':True,'packets':[p for p in [pdet,psub] if p is not None]}
    if output_context is not None:
        try:result['output']=output_metrics(w,c,target,m,bits,alpha,det,sub,output_context)
        except Exception as error:
            error.partial_result={**result,'quality_pass':False}
            raise
    return result

def sq(a):return float(np.einsum('ij,ij->',a,a))
def inner(a,b):return float(np.einsum('ij,ij->',a,b))

def prepare_output(w,c,x,z,require_projection=True):
    if x.shape!=z.shape or x.ndim!=2 or x.shape[0]!=w.shape[1] or x.shape[1]!=4096:raise ValueError('output input shape')
    if not np.isfinite(x).all() or not np.isfinite(z).all():raise ValueError('output finite input')
    y=w@x;a=w@(x-z);s=c@z;n=x.shape[1]
    d=sq(s)/n;h=inner(a,s)/n;ae=sq(a)/n
    defect=abs(h-d)/max(np.sqrt(ae*d),d,1e-30)
    if require_projection:require(defect<=1e-8,'calibration projection defect',{'D':d,'H':h,'A_energy':ae,'defect':defect},1.0,1e-8)
    return {'x':x,'z':z,'y':y,'a':a,'s':s,'n':n,'D':d,'H':h,'A_energy':ae,
            'projection_defect':defect,'G':z@z.T,'B':y@z.T,'Ysq':sq(y),'Zsq':sq(z)}

def closure(left,terms,original_terms=None,identity='output algebraic closure'):
    right=sum(terms);difference=left-right
    denominator=max((abs(left) if original_terms is None else sum(map(abs,original_terms)))+sum(map(abs,terms)),1e-30)
    require(abs(difference)<=1e-10*denominator,identity,{'left':left,'terms':terms,'original_terms':original_terms,'right':right,'difference':difference},denominator,1e-10)
    return {'direct':left,'reconstructed':right,'difference':difference,'denominator':denominator,'relative':abs(difference)/denominator}

def output_metrics(w,c,target,m,bits,alpha,det,sub,context):
    z=context['z'];y=context['y'];n=context['n'];a=context['a'];s=context['s']
    clipped=np.clip(target,-m[:,None],m[:,None]);j=(clipped-target)@z;res=a-alpha*s
    v=sq(j)/n;l=sq(res)/n;cross=inner(res,j)/n
    kappa=float(np.sum((2*m/(2**bits-1))**2/12))*context['Zsq']/n
    target_expected=v+kappa
    teacher_expected=sq(y-clipped@z)/n+kappa
    target_det=sq((det-target)@z)/n;target_sub=sq((sub-target)@z)/n
    teacher_det=sq(y-det@z)/n;teacher_sub=sq(y-sub@z)/n
    cauchy_left=abs(inner(s,j)/n);cauchy_right=np.sqrt(context['D']*v)
    require(cauchy_left<=cauchy_right+1e-10*max(cauchy_left,cauchy_right,1e-30),'N1.7 Cauchy guard',{'left':cauchy_left,'right':float(cauchy_right),'D':context['D'],'V':v},max(cauchy_left,cauchy_right,1e-30),1e-10)
    replay=[]
    for tag,q,direct_t,direct_y in [('deterministic',det,target_det,teacher_det),('single_seed',sub,target_sub,teacher_sub),('clipped_mean',clipped,v,teacher_expected-kappa)]:
        e=q-target;target_quad=inner(e@context['G'],e)/n
        td=max(direct_t,abs(target_quad),1e-30)
        require(abs(direct_t-target_quad)<=1e-10*td,'target sufficient-statistic replay',{'mode':tag,'direct':direct_t,'quadratic':target_quad},td,1e-10)
        qenergy=inner(q@context['G'],q);ycross=inner(q,context['B'])
        yquad=(context['Ysq']-2*ycross+qenergy)/n
        yd=max(context['Ysq']+abs(qenergy)+2*abs(ycross),1e-30)/n
        require(abs(direct_y-yquad)<=1e-10*yd,'teacher sufficient-statistic replay',{'mode':tag,'direct':direct_y,'quadratic':yquad,'Ysq':context['Ysq'],'qenergy':qenergy,'ycross':ycross},yd,1e-10)
        replay.append({'mode':tag,'target_direct':direct_t,'target_replay':target_quad,'target_denominator':td,'teacher_direct':direct_y,'teacher_replay':yquad,'teacher_denominator':yd})
    return {'split':'calibration','tokens':n,'D':context['D'],'H':context['H'],'A_energy':context['A_energy'],
            'projection_defect':context['projection_defect'],'V':v,'L':l,'residual_J_inner':cross,
            'A_J_inner':inner(a,j)/n,'S_J_inner':inner(s,j)/n,'kappa':kappa,
            'any_target_overload':bool(np.any(target!=clipped)),
            'target_reconstruction':{'expected':target_expected,'deterministic':target_det,'single_seed':target_sub,'ratio':ratio(target_expected,target_det)},
            'teacher_local_loss':{'expected':teacher_expected,'deterministic':teacher_det,'single_seed':teacher_sub,'ratio':ratio(teacher_expected,teacher_det)},
            'teacher_expected_closure':closure(teacher_expected,[l,-2*cross,v,kappa]),
            'N1_7_fixed_target':{'absolute_cross':cauchy_left,'cauchy_bound':float(cauchy_right)},
            'sufficient_statistics_replay':replay}

def attach_alpha_comparisons(rows):
    for bits in [2,3,4]:
        rs=[r for r in rows if r['bits']==bits]
        base=next(r['output'] for r in rs if r['alpha']==0)
        assert base['V']==0 and base['residual_J_inner']==0
        for row in rs:
            a=row['alpha'];o=row['output']
            if o['kappa']!=base['kappa']:raise ValueError('alpha-dependent analytic noise')
            df=o['teacher_local_loss']['expected']-base['teacher_local_loss']['expected']
            generic_fixed=a*a*o['D']-2*a*o['H'];projected_fixed=-a*(2-a)*o['D']
            other=[-2*o['residual_J_inner'],o['V'],2*base['A_J_inner'],-base['V']]
            generic=closure(df,[generic_fixed,*other],original_terms=[o['teacher_local_loss']['expected'],base['teacher_local_loss']['expected']],identity='generic alpha difference closure')
            gap=generic_fixed-projected_fixed
            bound=2*np.sqrt(o['L']*o['V'])+o['V']+2*np.sqrt(base['L']*base['V'])+base['V']
            lhs=abs(df-generic_fixed)
            bound_scale=max(abs(o['teacher_local_loss']['expected'])+abs(base['teacher_local_loss']['expected'])+abs(generic_fixed)+abs(bound),1e-30)
            require(lhs<=bound+1e-10*bound_scale,'N1.6 generic bound',{'lhs':lhs,'bound':float(bound),'Falpha':o['teacher_local_loss']['expected'],'F0':base['teacher_local_loss']['expected'],'generic_fixed':generic_fixed},bound_scale,1e-10)
            o['alpha_difference']={'direct':df,'generic_fixed':generic_fixed,'projected_fixed':projected_fixed,
                'projection_gap':gap,'generic_closure':generic,'projected_reconstruction':projected_fixed+sum(other),
                'projected_discrepancy':df-(projected_fixed+sum(other)),
                'N1_6_lhs':lhs,'N1_6_rhs':float(bound),'N1_6_guard_scale':bound_scale}
