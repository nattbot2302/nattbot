import sys, json, gzip, datetime as dt
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, ".")
import bot
now = dt.datetime.now(bot.UTC)
def one(L):
    slug, name, cal = L
    try:
        fin, allm = bot.fetch_league(slug, now)
    except Exception as e:
        return slug, {"err": str(e)}
    def ser(m):
        m = dict(m); m["date"] = m["date"].isoformat(); m.pop("_coef", None); return m
    return slug, {"name": name, "cal": cal, "allm": [ser(m) for m in allm]}
with ThreadPoolExecutor(6) as ex:
    out = dict(ex.map(one, bot.LEAGUES))
out["_now"] = now.isoformat()
with gzip.open("veri.json.gz", "wt", encoding="utf-8") as f:
    json.dump(out, f, ensure_ascii=False)
print({k: (len(v["allm"]) if isinstance(v, dict) and "allm" in v else v) for k, v in out.items()})
