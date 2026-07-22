from flask import Flask, request, jsonify
from flask_cors import CORS
import math, traceback, json, copy, os
from datetime import datetime

app = Flask(__name__)
CORS(app)

# ==== CONFIG ====
KAP = {'CDE':{'kg':1000,'cbm':4},'CDD':{'kg':3000,'cbm':18},'Fuso':{'kg':8000,'cbm':40},
       'Blind_Van':{'kg':800,'cbm':6},'Blind Van':{'kg':800,'cbm':6}}
SEWA = {'CDE':9000000,'CDD':12000000,'Fuso':18000000,'Blind_Van':3500000,'Blind Van':3500000}

def hv(lat1,lon1,lat2,lon2):
    R=6371;lat1,lat2=math.radians(lat1),math.radians(lat2)
    dlat=math.radians(lat2-lat1);dlon=math.radians(lon2-lon1)
    a=math.sin(dlat/2)**2+math.cos(lat1)*math.cos(lat2)*math.sin(dlon/2)**2
    return R*2*math.atan2(math.sqrt(a),math.sqrt(1-a))

def cbm(p,l,t):return(p/1000)*(l/1000)*(t/1000)if all([p,l,t])else 0

def sewa_h(tipe,pp):
    hk=pp.get('hari_kerja_per_bulan',25);sb=pp.get('sewa_kendaraan_per_bulan',{})
    if tipe in sb:return sb[tipe]/hk
    if tipe in SEWA:return SEWA[tipe]/hk
    tl=tipe.lower().replace('_',' ')if tipe else''
    for k,v in SEWA.items():
        if k.lower().replace('_',' ')==tl:return v/hk
    return SEWA.get('CDE',9000000)/hk

def calc_orders(orders,mbi):
    lu={}
    for bi in mbi:
        k=(bi.get('brand'),bi.get('item'))
        if k[0]and k[1]:lu[k]={'cbm':cbm(bi.get('panjang_mm',0),bi.get('lebar_mm',0),bi.get('tinggi_mm',0)),'berat':bi.get('berat_per_pcs_gram',0)/1000,'harga':bi.get('harga_per_pcs',0)}
    ts={}
    for o in orders:
        k=(o.get('brand'),o.get('item'));q=o.get('qty_pcs',0)
        if not all([o.get('id_toko'),k[0],k[1],q])or k not in lu:continue
        tid=o['id_toko'];info=lu[k]
        if tid not in ts:ts[tid]={'items':[],'total_berat_kg':0,'total_cbm':0,'total_harga':0}
        tc=info['cbm']*q;tb=info['berat']*q;th=info['harga']*q
        ts[tid]['items'].append({'brand':k[0],'item':k[1],'qty':q,'cbm':round(tc,4),'berat':round(tb,2),'harga':th})
        ts[tid]['total_berat_kg']+=tb;ts[tid]['total_cbm']+=tc;ts[tid]['total_harga']+=th
    return ts

def precompute(tl,dc):
    jd={t['id_toko']:hv(dc[0],dc[1],t['latitude'],t['longitude'])for t in tl}
    jtt={}
    for i,t1 in enumerate(tl):
        for t2 in tl[i+1:]:
            d=hv(t1['latitude'],t1['longitude'],t2['latitude'],t2['longitude'])
            jtt[(t1['id_toko'],t2['id_toko'])]=d;jtt[(t2['id_toko'],t1['id_toko'])]=d
    return jd,jtt

def nn_route(tids,dc,tc,jtt,jd):
    if not tids:return[],0
    uv=set(tids);rt=[];cid='DEPOT';tj=0
    while uv:
        nn=None;nd=float('inf')
        for tid in uv:
            d=jd.get(tid,float('inf'))if cid=='DEPOT'else jtt.get((cid,tid),float('inf'))
            if d<nd:nd=d;nn=tid
        rt.append(nn);tj+=nd;cid=nn;uv.remove(nn)
    if rt:
        last=tc.get(rt[-1],dc)
        tj+=hv(last[0],last[1],dc[0],dc[1])
    return rt,tj

def check_tw(rt,dc,tdl,jtt,jd,kec,wb):
    at=480;pid='DEPOT'
    for tid in rt:
        d=jd.get(tid,0)if pid=='DEPOT'else jtt.get((pid,tid),0)
        at+=(d/kec)*60;ti=tdl.get(tid,{})
        if at<ti.get('buka',480):at=ti.get('buka',480)
        if at>ti.get('tutup',1020):return False
        at+=ti.get('waktu_bongkar_menit',wb);pid=tid
    return True

def b3pl(tl,p3):
    t=0;bd=p3.get('biaya_dasar_per_titik',0);bp=p3.get('biaya_per_kg',0)
    for x in tl:t+=bd+x.get('total_berat',0)*bp+x.get('biaya_bongkar_muat',0)+x.get('biaya_parkir',0)+x.get('biaya_tol_per_toko',0)
    return t

def bint(jr,tipe,pp):
    return jr*pp.get('konsumsi_bbm_per_km',0.15)*pp.get('harga_bbm_per_liter',10000)+pp.get('gaji_driver_per_bulan',8000000)/pp.get('hari_kerja_per_bulan',25)+sewa_h(tipe,pp)

def batch_v32(ts,arm,mt,pp,p3,f3=None,mc=8,mb=6):
    act=[v for v in arm if v.get('status','aktif').lower()=='aktif']
    if not act:return[],[],{}
    dep=next((t for t in mt if t.get('jenis')=='depo'or t.get('id_toko')=='DC-Solo'),mt[0])
    dc=(float(dep.get('latitude',0)),float(dep.get('longitude',0)))
    md={};tc={};tdl={}
    for t in mt:
        tid=t.get('id_toko')
        if tid:md[tid]=t;tc[tid]=(float(t.get('latitude',0)),float(t.get('longitude',0)));tdl[tid]=t
    tl=[]
    for tid,s in ts.items():
        if tid==dep.get('id_toko'):continue
        t=md.get(tid,{});lat,lng=tc.get(tid,(0,0))
        k=t.get('kendaraan_diizinkan',[0,1])
        if isinstance(k,str):
            try:k=json.loads(k)
            except:
                try:k=[int(x.strip())for x in k.split(',')]
                except:k=[0,1]
        b=int(t.get('buka',480)or 480);tu=int(t.get('tutup',1020)or 1020)
        tl.append({'id_toko':tid,'total_berat':s['total_berat_kg'],'total_cbm':s['total_cbm'],'latitude':lat,'longitude':lng,
                   'jarak':hv(dc[0],dc[1],lat,lng),'wbm':t.get('waktu_bongkar_menit',30)or 30,'kend':k,'buka':b,'tutup':tu,
                   'tol':t.get('biaya_tol_per_toko',0)or 0,'parkir':t.get('biaya_parkir',0)or 0,'bm':t.get('biaya_bongkar_muat',0)or 0})
    jd,jtt=precompute(tl,dc)
    bv=None;cdd=None
    for v in act:
        tp=v.get('tipe','').lower().replace('_',' ')
        if'blind'in tp or'van'in tp:bv=v
        elif'cdd'in tp or'cde'in tp or'fuso'in tp:cdd=v
    if not bv and len(act)>=1:bv=act[0]
    if not cdd and len(act)>=2:cdd=act[-1]
    elif not cdd:cdd=bv
    bvk=bv.get('kapasitas_kg',KAP.get(bv.get('tipe','Blind_Van'),{}).get('kg',800))if bv else 800
    bvc=bv.get('kapasitas_cbm',KAP.get(bv.get('tipe','Blind_Van'),{}).get('cbm',6))if bv else 6
    bvj=bv.get('jam_kerja',8)if bv else 8;bvt=bv.get('tipe','Blind_Van')if bv else'Blind_Van';bvp=bv.get('plat_nomor','BV_1')if bv else'BV_1'
    cdk=cdd.get('kapasitas_kg',KAP.get(cdd.get('tipe','CDD'),{}).get('kg',3000))if cdd else 3000
    cdc=cdd.get('kapasitas_cbm',KAP.get(cdd.get('tipe','CDD'),{}).get('cbm',18))if cdd else 18
    cdj=cdd.get('jam_kerja',8)if cdd else 8;cdt=cdd.get('tipe','CDD')if cdd else'CDD';cdp=cdd.get('plat_nomor','CDD_1')if cdd else'CDD_1'
    kec=pp.get('kecepatan_km_per_jam',40);wb=pp.get('waktu_bongkar_per_toko_menit',30);jkn=pp.get('jam_kerja_normal',8)
    pl=[];internal=tl.copy()
    if f3:
        for t in tl:
            if t['jarak']>f3:pl.append(t)
            else:internal.append(t)
    bv_cand=[];cdd_cand=[];both=[];pl_only=[]
    for t in internal:
        k=t.get('kend',[0,1])
        if k==[]or k==[2]or k=='3pl':pl_only.append(t)
        elif k==[0]:cdd_cand.append(t)
        elif k==[1]:bv_cand.append(t)
        else:both.append(t)
    pl.extend(pl_only);both.sort(key=lambda x:x['jarak'])
    bv_t=[];bkg=0;bcb=0
    for t in both[:]:
        if bkg+t['total_berat']<=bvk and bcb+t['total_cbm']<=bvc:bv_t.append(t);bkg+=t['total_berat'];bcb+=t['total_cbm'];both.remove(t)
    bv_ovf=[]
    for t in bv_cand:
        if bkg+t['total_berat']<=bvk and bcb+t['total_cbm']<=bvc:bv_t.append(t);bkg+=t['total_berat'];bcb+=t['total_cbm']
        else:bv_ovf.append(t)
    if bkg<bvk*0.7 and both:
        both.sort(key=lambda x:x['total_berat'])
        for t in both[:]:
            if bkg+t['total_berat']<=bvk and bcb+t['total_cbm']<=bvc:bv_t.append(t);bkg+=t['total_berat'];bcb+=t['total_cbm'];both.remove(t)
    cdd_pool=cdd_cand+both+bv_ovf;cdd_pool.sort(key=lambda x:x['jarak'])
    cdd_trips=[];rem_cdd=cdd_pool.copy()
    while rem_cdd:
        trip=[];tkg=0;tcb=0;tids=[]
        for t in rem_cdd[:]:
            if tkg+t['total_berat']>cdk or tcb+t['total_cbm']>cdc or len(trip)>=mc:continue
            ej=sum(jd.get(tid,0)for tid in tids+[t['id_toko']]);ew=(ej/kec)+(len(trip)+1)*wb/60
            if ew>jkn*1.2:continue
            trip.append(t);tkg+=t['total_berat'];tcb+=t['total_cbm'];tids.append(t['id_toko']);rem_cdd.remove(t)
        if trip:cdd_trips.append({'toko_list':trip,'total_berat':tkg,'total_cbm':tcb})
        else:break
    bv_trips=[];rem_bv=bv_t.copy();hari=1
    while rem_bv:
        wh=0.0
        while wh<bvj-0.5:
            trip=[];tkg=0;tcb=0;tids=[]
            for t in rem_bv[:]:
                if tkg+t['total_berat']>bvk or tcb+t['total_cbm']>bvc or len(trip)>=mb:continue
                ej=sum(jd.get(tid,0)for tid in tids+[t['id_toko']]);ew=(ej/kec)+(len(trip)+1)*wb/60
                if wh+ew>bvj:break
                trip.append(t);tkg+=t['total_berat'];tcb+=t['total_cbm'];tids.append(t['id_toko']);rem_bv.remove(t)
            if trip:
                bv_trips.append({'toko_list':trip,'hari_ke':hari,'total_berat':tkg,'total_cbm':tcb})
                ej=sum(jd.get(tid,0)for tid in tids);ew=(ej/kec)+len(trip)*wb/60;wh+=ew
            else:break
        if not rem_bv:break
        hari+=1
    all_trips=[]
    for trip in bv_trips:
        tids=[t['id_toko']for t in trip['toko_list']];rt,ej=nn_route(tids,dc,tc,jtt,jd);bi=bint(ej,bvt,pp);b3=b3pl(trip['toko_list'],p3)
        if bi>b3:pl.extend(trip['toko_list']);continue
        if not check_tw(rt,dc,tdl,jtt,jd,kec,wb):
            if len(trip['toko_list'])>1:pl.append(trip['toko_list'][-1]);trip['toko_list']=trip['toko_list'][:-1];tids=[t['id_toko']for t in trip['toko_list']];rt,ej=nn_route(tids,dc,tc,jtt,jd)
            else:pl.extend(trip['toko_list']);continue
        all_trips.append({'trip_ke':len(all_trips)+1,'armada':bvp,'tipe_kendaraan':bvt,'hari_ke':trip['hari_ke'],'jumlah_toko':len(trip['toko_list']),
                          'total_berat_kg':round(trip['total_berat'],2),'total_cbm':round(trip['total_cbm'],4),'estimasi_waktu_jam':round((ej/kec)+len(trip['toko_list'])*wb/60,1),
                          'jarak_km':round(ej,1),'biaya_internal_rp':round(bi,2),'biaya_3pl_rp':round(b3,2),'lebih_murah_3pl':bi>b3,'penghematan_rp':round(b3-bi,2),'toko_ids':rt})
    hari_cdd=1
    for trip in cdd_trips:
        tids=[t['id_toko']for t in trip['toko_list']];rt,ej=nn_route(tids,dc,tc,jtt,jd);bi=bint(ej,cdt,pp);b3=b3pl(trip['toko_list'],p3)
        if bi>b3:pl.extend(trip['toko_list']);continue
        if not check_tw(rt,dc,tdl,jtt,jd,kec,wb):
            if len(trip['toko_list'])>1:pl.append(trip['toko_list'][-1]);trip['toko_list']=trip['toko_list'][:-1];tids=[t['id_toko']for t in trip['toko_list']];rt,ej=nn_route(tids,dc,tc,jtt,jd)
            else:pl.extend(trip['toko_list']);continue
        all_trips.append({'trip_ke':len(all_trips)+1,'armada':cdp,'tipe_kendaraan':cdt,'hari_ke':hari_cdd,'jumlah_toko':len(trip['toko_list']),
                          'total_berat_kg':round(trip['total_berat'],2),'total_cbm':round(trip['total_cbm'],4),'estimasi_waktu_jam':round((ej/kec)+len(trip['toko_list'])*wb/60,1),
                          'jarak_km':round(ej,1),'biaya_internal_rp':round(bi,2),'biaya_3pl_rp':round(b3,2),'lebih_murah_3pl':bi>b3,'penghematan_rp':round(b3-bi,2),'toko_ids':rt})
        hari_cdd+=1
    th=max([t['hari_ke']for t in all_trips])if all_trips else 0;tw=sum(t['estimasi_waktu_jam']for t in all_trips);tbi=sum(t['biaya_internal_rp']for t in all_trips)
    jl=sum(max(0,t['estimasi_waktu_jam']-jkn)for t in all_trips);mw=max((t['estimasi_waktu_jam']for t in all_trips),default=0);b3t=b3pl(pl,p3);ttd=sum(t['jumlah_toko']for t in all_trips)
    return all_trips,pl,{'total_toko_dikirim':ttd,'jumlah_trip':len(all_trips),'total_hari_kerja':th,'total_waktu_jam':round(tw,1),'jam_kerja_normal':jkn,'jam_lembur':round(jl,1),
                         'max_waktu_per_trip_jam':round(mw,1),'total_biaya_internal_rp':round(tbi,2),'total_penghematan_rp':round(sum(t['penghematan_rp']for t in all_trips if t['penghematan_rp']>0),2),
                         'jumlah_toko_3pl':len(pl),'biaya_3pl_dilempar_rp':round(b3t,2),'total_biaya_keseluruhan_rp':round(tbi+b3t,2)}

@app.route('/')
def index():return jsonify({"status":"online","service":"TMS v3.2","version":"3.2.0","endpoints":["/hitung-rute-multi","/hitung-rute","/debug-cbm","/health"]})

@app.route('/health')
def health():return jsonify({"status":"healthy","timestamp":datetime.now().isoformat()})

@app.route('/hitung-rute-multi',methods=['POST'])
def hitung_rute_multi():
    try:
        data=request.json
        if not data:return jsonify({"status":"gagal","pesan":"Request body kosong"}),400
        pp=data.get('parameter_pengiriman',{});p3=data.get('parameter_3pl',{});ar=data.get('armada',[]);mt=data.get('master_toko',[]);mbi=data.get('master_brand_item',[]);orders=data.get('orders',[])
        f3=data.get('force_3pl_jarak_km');mc=data.get('max_toko_per_trip_cdd',8);mb=data.get('max_toko_per_trip_bv',6)
        if not ar or not mt or not orders:return jsonify({"status":"gagal","pesan":"Data tidak lengkap"}),400
        ts=calc_orders(orders,mbi)
        if not ts:return jsonify({"status":"gagal","pesan":"Tidak ada order valid"})
        dep=next((t for t in mt if t.get('jenis')=='depo'or t.get('id_toko')=='DC-Solo'),mt[0]);dc=(float(dep.get('latitude',0)),float(dep.get('longitude',0)))
        all_trips,pl,summary=batch_v32(ts,ar,mt,pp,p3,f3=f3,mc=mc,mb=mb)
        twd=[]
        for trip in all_trips:
            td=copy.deepcopy(trip);td['toko_detail']=[{'id_toko':tid,'nama_toko':next((t.get('nama_toko','Unknown')for t in mt if t.get('id_toko')==tid),'Unknown'),'latitude':next((t.get('latitude',0)for t in mt if t.get('id_toko')==tid),0),'longitude':next((t.get('longitude',0)for t in mt if t.get('id_toko')==tid),0)}for tid in trip['toko_ids']];twd.append(td)
        t3d=[]
        for t in pl:
            tid=t['id_toko']if isinstance(t,dict)else t
            for m in mt:
                if m.get('id_toko')==tid:lat,lng=float(m.get('latitude',0)),float(m.get('longitude',0));t3d.append({'id_toko':tid,'nama_toko':m.get('nama_toko','Unknown'),'latitude':lat,'longitude':lng,'jarak_dari_depot':round(hv(dc[0],dc[1],lat,lng),2)});break
        return jsonify({"status":"sukses","version":"3.2.0","summary":summary,"trips":twd,"dilempar_ke_3pl":[t['id_toko']if isinstance(t,dict)else t for t in pl],"toko_3pl_detail":t3d})
    except Exception as e:return jsonify({"status":"gagal","pesan":f"Internal error: {str(e)}","trace":traceback.format_exc()}),500

@app.route('/hitung-rute',methods=['POST'])
def hitung_rute():
    try:
        data=request.json
        if not data:return jsonify({"status":"gagal","pesan":"Request body kosong"}),400
        pp=data.get('parameter_pengiriman',{});p3=data.get('parameter_3pl',{});ar=data.get('armada',[]);mt=data.get('master_toko',[]);mbi=data.get('master_brand_item',[]);orders=data.get('orders',[])
        if not ar or not mt or not orders:return jsonify({"status":"gagal","pesan":"Data tidak lengkap"}),400
        ts=calc_orders(orders,mbi)
        if not ts:return jsonify({"status":"gagal","pesan":"Tidak ada order valid"})
        dep=next((t for t in mt if t.get('jenis')=='depo'or t.get('id_toko')=='DC-Solo'),mt[0]);dc=(float(dep.get('latitude',0)),float(dep.get('longitude',0)))
        all_trips,pl,summary=batch_v32(ts,ar,mt,pp,p3)
        t3d=[]
        for t in pl:
            tid=t['id_toko']if isinstance(t,dict)else t
            for m in mt:
                if m.get('id_toko')==tid:lat,lng=float(m.get('latitude',0)),float(m.get('longitude',0));t3d.append({'id_toko':tid,'nama_toko':m.get('nama_toko','Unknown'),'latitude':lat,'longitude':lng,'jarak_dari_depot':round(hv(dc[0],dc[1],lat,lng),2)});break
        return jsonify({"status":"sukses","version":"3.2.0","summary":summary,"trips":all_trips,"dilempar_ke_3pl":[t['id_toko']if isinstance(t,dict)else t for t in pl],"toko_3pl_detail":t3d})
    except Exception as e:return jsonify({"status":"gagal","pesan":f"Internal error: {str(e)}","trace":traceback.format_exc()}),500

@app.route('/debug-cbm',methods=['POST'])
def debug_cbm():
    try:
        data=request.json
        if not data:return jsonify({"status":"gagal","pesan":"Request body kosong"}),400
        orders=data.get('orders',[]);mbi=data.get('master_brand_item',[]);mt=data.get('master_toko',[])
        if not orders or not mbi:return jsonify({"status":"gagal","pesan":"Data tidak lengkap"}),400
        ts=calc_orders(orders,mbi);result=[]
        for tid,s in ts.items():
            md=next((t for t in mt if t.get('id_toko')==tid),None)
            ci=sum(i.get('cbm',0)for i in s['items']);bi=sum(i.get('berat',0)for i in s['items'])
            result.append({'id_toko':tid,'nama_toko':md.get('nama_toko','Unknown')if md else'Unknown','latitude':md.get('latitude',0)if md else 0,'longitude':md.get('longitude',0)if md else 0,
                           'total_berat_kg':round(s['total_berat_kg'],2),'total_cbm':round(s['total_cbm'],4),'total_cbm_dari_items':round(ci,4),'selisih_cbm':round(s['total_cbm']-ci,4),
                           'total_berat_dari_items':round(bi,2),'jumlah_items':len(s['items']),'items':s['items']})
        return jsonify({"status":"sukses","summary":{"jumlah_toko":len(result),"total_berat_semua_kg":round(sum(r['total_berat_kg']for r in result),2),"total_cbm_semua":round(sum(r['total_cbm']for r in result),4)},"toko":result})
    except Exception as e:return jsonify({"status":"gagal","pesan":f"Internal error: {str(e)}","trace":traceback.format_exc()}),500

if __name__=='__main__':
    port=int(os.environ.get('PORT',5000))
    app.run(host='0.0.0.0',port=port,debug=False)
