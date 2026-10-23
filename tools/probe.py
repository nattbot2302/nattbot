import requests, json
out = {}
for slug in ["wal.1", "irl.1", "nir.1", "irl.2", "fra.2"]:
    for d in ["20261018", "20261010", "20260920", "20260301"]:
        try:
            r = requests.get(f"https://site.api.espn.com/apis/site/v2/sports/soccer/{slug}/scoreboard", params={"dates": d}, timeout=20)
            j = r.json() if r.ok else {}
            evs = j.get("events", [])
            out[f"{slug} {d}"] = [r.status_code, len(evs), (j.get("leagues") or [{}])[0].get("name"), [e.get("name") for e in evs[:2]]]
        except Exception as e:
            out[f"{slug} {d}"] = str(e)
print(json.dumps(out, ensure_ascii=False, indent=1))
