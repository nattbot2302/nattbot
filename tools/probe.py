import requests, json, time
SLUGS = ["por.1","por.2","tur.1","tur.2","ita.2","esp.2","fra.3","ger.3","eng.5","sco.2","sco.3","bel.2","sui.1","sui.2","aut.2","cze.1","pol.1","rou.1","srb.1","cro.1","hun.1","ukr.1","isr.1","cyp.1","bul.1","svk.1","slo.1","fin.1","swe.2","nor.2","den.2","irl.1","arg.1","arg.2","mex.1","mex.2","bra.2","col.1","chi.1","uru.1","ecu.1","par.1","per.1","usa.2","usa.usl.1","can.1","kor.1","jpn.2","chn.2","ind.1","tha.1","idn.1","aus.2","egy.1","rsa.1","mar.1","ksa.2","uae.1","qat.1","bra.camp.paulista"]
DATES = ["20261025", "20261019", "20260927"]
out = {}
for s in SLUGS:
    row = []
    for d in DATES:
        try:
            r = requests.get(f"https://site.api.espn.com/apis/site/v2/sports/soccer/{s}/scoreboard", params={"dates": d}, timeout=20)
            if not r.ok: row.append(f"HTTP{r.status_code}"); continue
            j = r.json(); evs = j.get("events", [])
            done = sum(1 for e in evs if e.get("status", {}).get("type", {}).get("completed"))
            stats = sum(1 for e in evs for c in e["competitions"][0]["competitors"] if c.get("statistics"))
            det = sum(1 for e in evs if e["competitions"][0].get("details"))
            row.append([len(evs), done, stats, det, (j.get("leagues") or [{}])[0].get("name")])
        except Exception as e:
            row.append(str(e)[:40])
        time.sleep(0.3)
    out[s] = row
print(json.dumps(out, ensure_ascii=False))
