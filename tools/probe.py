import requests, json
want = {"401874779","401875566","401878961","401882829","401882832","401896740","401896742"}
out = {}
for slug in ["esp.1", "bel.1", "gre.1", "ita.1", "ned.1"]:
    r = requests.get(f"https://site.api.espn.com/apis/site/v2/sports/soccer/{slug}/scoreboard", params={"dates": "20261025"}, timeout=20)
    for ev in (r.json().get("events", []) if r.ok else []):
        if ev["id"] not in want: continue
        c = ev["competitions"][0]
        row = {}
        for x in c["competitors"]:
            st = {s["name"]: s.get("displayValue") for s in x.get("statistics", [])}
            row[x["homeAway"]] = {"t": x["team"].get("shortDisplayName"), "g": x.get("score"), "sh": st.get("totalShots"), "sot": st.get("shotsOnTarget"), "pos": st.get("possessionPct"), "cor": st.get("wonCorners")}
        row["goals"] = [(d.get("clock", {}).get("displayValue"), (d.get("team") or {}).get("id"), d.get("penaltyKick"), d.get("ownGoal")) for d in c.get("details", []) if d.get("scoringPlay")]
        row["red"] = [(d.get("clock", {}).get("displayValue"), (d.get("team") or {}).get("id")) for d in c.get("details", []) if d.get("redCard")]
        out[ev["id"]] = row
print(json.dumps(out, ensure_ascii=False, indent=1))
