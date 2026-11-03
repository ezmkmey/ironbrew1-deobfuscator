local api = ...
local env, chn, rg, isp, st = api.E, api.CHAIN, api.R, api.isP, api.ST or {}

local reg = setmetatable({}, { __mode = "k" })
local upv = setmetatable({}, { __mode = "k" })
local first = {}
local ordr = {}
local ordidx = {}
local precall = false
local curord = nil
local caps = {}
local seen = {}

local function ibf(f, loc, up)
	if reg[f] == nil then
		reg[f] = loc
		ordr[#ordr + 1] = f
		ordidx[f] = #ordr
		if first[loc] == nil then first[loc] = f end
	end
	if up ~= nil and upv[f] == nil then upv[f] = up end
	return f
end

local curpc = nil
local zfpc = setmetatable({}, { __mode = "k" })
local pcproto = {}
local cntn = {}
local cntmulti = {}
local mkt, mkstk, mkpc, mka, mkprv, mklow, mkrun = nil, nil, nil, nil, nil, nil, nil
local mkn, mktot = 0, 0
local mksnap = {}
local function mksave(t)
	if type(t) ~= "table" or mksnap[t] ~= nil then return end
	local s = {}
	for k, a in next, t do
		if type(a) == "table" then s[k] = table.clone(a) end
	end
	mksnap[t] = s
end
local function ibmk(t, stk)
	if mkt ~= nil or type(t) ~= "table" or type(stk) ~= "table" then return end
	mkt, mkstk = t, stk
	mksave(t)
end
local function setpc(pc, t)
	curpc = pc
	if t == nil or t ~= mkt or mkpc ~= nil then return end
	if mka == nil then
		for k, v in next, mkstk do
			if type(k) == "number" and type(v) == "table" and rawget(v, 1) == mkt then mka = k end
		end
		if mka == nil then return end
		mklow = {}
		for i = 0, mka - 1 do
			mklow[i] = rawget(mkstk, i)
			if mklow[i] ~= nil then mkn += 1 end
		end
	else
		local n = -1
		if mka > mktot then
			n, mktot = 0, 0
			for k, v in next, mkstk do
				mktot += 1
				if n >= 0 and type(k) == "number" and k >= 0 and k <= mka - 1 and k % 1 == 0 then
					if rawequal(v, mklow[k]) then n += 1 else n = -1 end
				end
			end
		end
		if n ~= mkn then
			for i = 0, mka - 1 do
				if rawget(mkstk, i) ~= mklow[i] then
					mkpc = mkrun
					return
				end
			end
		end
	end
	if mkprv == nil or pc ~= mkprv + 1 then mkrun = pc end
	mkprv = pc
end
rawset(env, "__IBMK", ibmk)
local function zfpcrec(zf)
	if type(zf) == "table" and type(curpc) == "number" and zfpc[zf] == nil then zfpc[zf] = curpc end
end
rawset(env, "__SETPC", setpc)
rawset(env, "__ZFPC", zfpcrec)

local p2 = false
local caps2 = {}
local seen2 = {}
local pcproto2 = {}
local cntn2 = {}
local cntmulti2 = {}
local p2inp = { 1, 2, 3, 4, 5, 6 }

local prelst = {}
do
	local spec = api.CFG and api.CFG.precall
	if type(spec) == "table" then
		for _, n in spec do
			local v = tonumber(n)
			if v ~= nil then prelst[#prelst + 1] = v end
		end
	end
end

local function forceret(...)
	local f = (...)
	if type(f) == "function" then
		p2 = true
		for _, i in p2inp do pcall(f, i) end
		p2 = false
	end
	return ...
end
rawset(env, "__FORCERET", forceret)

local inann = false
local annseen = {}
local function ibc(mk, params, vars, ann, t1)
	if inann then return end
	if t1 ~= nil then mksave(t1) end
	local p, zf = params[1], params[2]
	if p2 then
		if type(p) == "table" and type(zf) == "table" and zfpc[zf] ~= nil then
			local pc = zfpc[zf]
			if type(pc) == "number" and pcproto[pc] == nil and pcproto2[pc] == nil then pcproto2[pc] = p end
			local n = 0
			for k in next, zf do if type(k) == "number" and k > n then n = k end end
			if cntn[n] == nil then
				if cntn2[n] == nil then cntn2[n] = p
				elseif cntn2[n] ~= p then cntmulti2[n] = true end
			end
		end
		if type(p) == "table" then
			if seen[p] or seen2[p] then return end
			seen2[p] = true
		end
		caps2[#caps2 + 1] = { mk = mk, params = params, vars = vars, ann = ann, order = curord }
		return
	end
	if type(p) == "table" and type(zf) == "table" and zfpc[zf] ~= nil then
		local pc = zfpc[zf]
		if type(pc) == "number" and pcproto[pc] == nil then pcproto[pc] = p end
		local n = 0
		for k in next, zf do if type(k) == "number" and k > n then n = k end end
		if cntn[n] == nil then cntn[n] = p
		elseif cntn[n] ~= p then cntmulti[n] = true end
	end
	if type(p) == "table" then
		if seen[p] then return end
		seen[p] = true
	end
	caps[#caps + 1] = { mk = mk, params = params, vars = vars, ann = ann }
end
rawset(env, "__IBF", ibf)
rawset(env, "__IBC", ibc)

local fnm = {}
local function namelib(pfx, t)
	for k, v in next, t do
		if type(v) == "function" and fnm[v] == nil and type(k) == "string" then fnm[v] = pfx .. k end
	end
end

local function sig(t)
	local ks = {}
	for k in next, t do
		if type(k) ~= "number" and type(k) ~= "string" then return nil end
		ks[#ks + 1] = tostring(k)
	end
	table.sort(ks)
	return table.concat(ks, ",")
end

local function force()
	local sigs = {}
	for _, c in caps do
		local p = c.params[1]
		if type(p) == "table" then
			local s = sig(p)
			if s and s ~= "" then sigs[s] = c end
		end
	end
	local calls = 0
	local round = 0
	chn.unlimited = true
	local sw = rawget(env, "__SPIN")
	if type(sw) == "table" then sw.step = math.huge end
	repeat
		round += 1
		local bfr = #caps
		local vis = {}
		local todo = {}
		for _, c in caps do
			for _, v in next, c.vars do
				if type(v) == "table" and not vis[v] and v ~= env then
					vis[v] = true
					todo[#todo + 1] = v
				end
			end
		end
		local i = 1
		while i <= #todo and i < 400000 do
			local t = todo[i]
			i += 1
			if not seen[t] then
				local s = sig(t)
				local c = s and sigs[s]
				if c and calls < 20000 then
					local maker = first[c.mk]
					if maker then
						calls += 1
						local args = table.clone(c.params)
						args[1] = t
						args[2] = nil
						local co = coroutine.create(maker)
						pcall(coroutine.resume, co, table.unpack(args, 1, math.max(3, #c.params)))
					end
				end
			end
			for k, v in next, t do
				if type(v) == "table" and not vis[v] and v ~= env and not isp(v) then
					vis[v] = true
					todo[#todo + 1] = v
				end
			end
		end
	until #caps == bfr or round > 20
end

local function mtrl()
	local done = {}
	for _, c in caps do
		for _, v in next, c.vars do
			if type(v) == "table" and not done[v] and v ~= env and not isp(v) and not annseen[v] then
				done[v] = true
				local mt = getmetatable(v)
				if type(mt) == "table" and rawget(mt, "__index") ~= nil then
					local hi = 0
					for k in next, v do if type(k) == "number" and k > hi and k < 1e7 then hi = k end end
					local miss = 0
					local k = 1
					while k <= hi or miss < 64 do
						if rawget(v, k) == nil then
							local ok, x = pcall(function() return v[k] end)
							if ok and x ~= nil then
								pcall(rawset, v, k, x)
								miss = 0
							elseif k > hi then
								miss += 1
							end
						end
						k += 1
					end
				end
			end
		end
	end
end

local function annc()
	local prs, seenk = {}, {}
	for _, c in caps do
		for _, kb in (c.ann or {}) do
			local kt, bx = c.vars[kb[1]], c.vars[kb[2]]
			if type(kt) == "table" and type(bx) == "table" and kt ~= env and not isp(kt) and not seenk[kt]
				and not table.isfrozen(kt) and not table.isfrozen(bx) then
				seenk[kt] = true
				annseen[kt] = true
				annseen[bx] = true
				prs[#prs + 1] = { kt, bx }
			end
		end
	end
	if #prs == 0 then return end
	local snap = {}
	local todo = {}
	local function visit(v)
		if type(v) == "table" and v ~= env and not isp(v) and snap[v] == nil and not table.isfrozen(v) then
			snap[v] = false
			todo[#todo + 1] = v
		end
	end
	for _, c in caps do
		for _, p in c.params do visit(p) end
		for _, v in next, c.vars do visit(v) end
	end
	local i = 1
	while i <= #todo do
		local t = todo[i]
		local s = {}
		for k, x in next, t do
			s[k] = x
			visit(k)
			visit(x)
		end
		snap[t] = s
		visit(getmetatable(t))
		i += 1
	end
	inann = true
	local savepc = curpc
	local got = {}
	for _, kb in prs do
		local kt, bx = kb[1], kb[2]
		local bfr = snap[kt] or {}
		local hi = 0
		for k in next, bfr do if type(k) == "number" and k > hi and k < 1e7 then hi = k end end
		local g = {}
		local saved = bx[1]
		local k, miss = 1, 0
		while (k <= hi or miss < 64) and k < 1e5 do
			if bfr[k] == nil then
				bx[1] = k
				local ok, x = pcall(function() return kt[k] end)
				if ok and x ~= nil then
					g[k] = x
					miss = 0
				elseif k > hi then
					miss += 1
				end
			end
			k += 1
		end
		bx[1] = saved
		got[kt] = g
	end
	curpc = savepc
	inann = false
	for t, s in next, snap do
		for k in next, t do if s[k] == nil then rawset(t, k, nil) end end
		for k, x in next, s do
			local y = rawget(t, k)
			if not rawequal(y, x) and (x == x or y == y) then rawset(t, k, x) end
		end
	end
	for kt, g in next, got do
		for k, x in next, g do
			if rawget(kt, k) == nil then rawset(kt, k, x) end
		end
	end
end

local function prx(c)
	local tabs, keys = {}, {}
	for _, v in next, c.vars do
		if type(v) == "table" and v ~= env and not isp(v) then
			tabs[#tabs + 1] = v
			local n = 0
			for _, x in next, v do
				n += 1
				if n > 32 then break end
			end
			if n <= 32 then
				for _, x in next, v do
					if type(x) == "string" or type(x) == "number" then keys[x] = true end
				end
			end
		end
	end
	local out = {}
	for _, pt in tabs do
		local mt = getmetatable(pt)
		if type(mt) == "table" and type(rawget(mt, "__index")) == "function" then
			local ok, px = pcall(function() return pt[1] end)
			local pmt = ok and type(px) == "table" and getmetatable(px)
			if type(pmt) == "table" and rawget(pmt, "__newindex") ~= nil then
				local map = {}
				for key in next, keys do
					local bfr = {}
					for i, tb in tabs do bfr[i] = rawget(tb, 1) end
					local snt = {}
					if pcall(function() px[key] = snt end) then
						for i, tb in tabs do
							if rawget(tb, 1) == snt then
								map[#map + 1] = { key, tb }
								rawset(tb, 1, bfr[i])
							end
						end
					end
				end
				if #map > 0 then out[#out + 1] = { pt, map } end
			end
		end
	end
	return out
end

local function hex(s)
	return (string.gsub(s, ".", function(ch) return string.format("%02x", string.byte(ch)) end))
end
local function num(x)
	if x ~= x then return '{"n":"nan"}' end
	if x == math.huge then return '{"n":"inf"}' end
	if x == -math.huge then return '{"n":"-inf"}' end
	if x == math.floor(x) and math.abs(x) < 2 ^ 53 then return string.format("%d", x) end
	return string.format("%.17g", x)
end

local function callrest()
	local skip = {}
	for _, c in caps do
		local m = first[c.mk]
		if m ~= nil then skip[m] = true end
	end
	local sw = rawget(env, "__SPIN")
	local svstep, svf, svn
	local bdg, wk = 0, 0
	if type(sw) == "table" then
		svstep, svf, svn = sw.step, sw.f, sw.n
		sw.step = 64
		sw.f = function()
			sw.n = 0
			bdg += 1
			wk += 1
			if bdg > (precall and 40000 or 64) then error("\0IBP3", 0) end
		end
	end
	local svunl = chn.unlimited
	chn.unlimited = true
	local wasp2 = p2
	p2 = true
	local snap = {}
	do
		local todo = {}
		local function visit(v)
			if type(v) == "table" and v ~= env and not isp(v) and snap[v] == nil and not table.isfrozen(v) then
				snap[v] = false
				todo[#todo + 1] = v
			end
		end
		for _, c in caps do
			for _, p in c.params do visit(p) end
			for _, v in next, c.vars do visit(v) end
		end
		local i = 1
		while i <= #todo do
			local t = todo[i]
			local s = {}
			for k, x in next, t do
				s[k] = x
				visit(k)
				visit(x)
			end
			snap[t] = s
			visit(getmetatable(t))
			i += 1
		end
	end

	local tgts = {}
	do
		local seent, added = {}, {}
		local function cmp(a, b)
			local ta, tb = type(a), type(b)
			if ta ~= tb then return ta < tb end
			if ta == "number" or ta == "string" then return a < b end
			return tostring(a) < tostring(b)
		end
		local function walk(t)
			if type(t) ~= "table" or seent[t] or t == env or isp(t) then return end
			seent[t] = true
			local ks = {}
			for k in next, t do ks[#ks + 1] = k end
			table.sort(ks, cmp)
			for _, k in ks do
				local v = rawget(t, k)
				local tv = type(v)
				if tv == "function" then
					if reg[v] ~= nil and not skip[v] and not added[v] then
						added[v] = true
						tgts[#tgts + 1] = v
					end
				elseif tv == "table" then
					walk(v)
				end
			end
			walk(getmetatable(t))
		end
		for _, c in caps do
			for _, p in c.params do walk(p) end
			local vks = {}
			for k in next, c.vars do vks[#vks + 1] = k end
			table.sort(vks, cmp)
			for _, k in vks do walk(c.vars[k]) end
		end
		for _, f in ordr do
			if not skip[f] and not added[f] then
				added[f] = true
				tgts[#tgts + 1] = f
			end
		end
	end
	local cnt = 0
	local calld = {}

	for _, i in prelst do
		if cnt >= 50000 or wk >= 2097152 then break end
		local f = ordr[i]
		if type(f) == "function" and not skip[f] and not calld[f] then
			calld[f] = true
			cnt += 1
			bdg = 0
			if type(sw) == "table" then sw.n = 0 end
			curord = i
			precall = true
			pcall(f, nil)
			precall = false
			curord = nil
		end
	end

	for round = 1, 4 do
		if #tgts == 0 then break end
		local mark = #ordr
		for _, f in tgts do
			if cnt >= 50000 or wk >= 2097152 then break end
			if not calld[f] then
				calld[f] = true
				cnt += 1
				bdg = 0
				if type(sw) == "table" then sw.n = 0 end
				curord = ordidx[f]
				pcall(f, nil)
				curord = nil
			end
		end
		local nxt = {}
		for i = mark + 1, #ordr do
			local f = ordr[i]
			if not skip[f] and not calld[f] then nxt[#nxt + 1] = f end
		end
		tgts = nxt
	end
	st.calls, st.work = cnt, wk
	for t, s in next, snap do
		if type(s) == "table" then
			for k in next, t do if s[k] == nil then rawset(t, k, nil) end end
			for k, x in next, s do
				local y = rawget(t, k)
				if not rawequal(y, x) and (x == x or y == y) then rawset(t, k, x) end
			end
		end
	end
	p2 = wasp2
	chn.unlimited = svunl
	if type(sw) == "table" then sw.step, sw.f, sw.n = svstep, svf, svn end
end

local function dump()
	local n2 = #caps2
	for i = 1, n2 do caps[#caps + 1] = caps2[i] end
	for p in next, seen2 do seen[p] = true end
	annc()
	callrest()
	for t, s in next, mksnap do
		for k, a in next, s do
			local b = rawget(t, k)
			if type(b) == "table" then
				for i in next, b do if a[i] == nil then b[i] = nil end end
				for i, v in next, a do b[i] = v end
			end
		end
	end
	for i = n2 + 1, #caps2 do caps[#caps + 1] = caps2[i] end
	for p in next, seen2 do seen[p] = true end
	for _, lib in { "string", "table", "math", "bit32", "coroutine", "buffer", "utf8", "os", "debug", "task" } do
		local t = rawget(env, lib)
		if type(t) == "table" then namelib(lib .. ".", t) end
		local rt = rg[lib] or _G[lib]
		if type(rt) == "table" then namelib(lib .. ".", rt) end
	end
	namelib("", env)
	local gnm = {}
	for k, v in next, env do
		if type(k) == "string" and (type(v) == "table" or type(v) == "userdata") and gnm[v] == nil
			and not string.find(k, "^__") then
			gnm[v] = k
		end
	end
	force()
	mtrl()
	annc()
	local pxs = {}
	for i, c in caps do
		local ok, r = pcall(prx, c)
		pxs[i] = ok and r or {}
	end
	local ids = {}
	local order = {}
	local sids, slist = {}, {}
	local ser = {}
	local function val(v)
		local t = type(v)
		if v == nil then return "null" end
		if t == "boolean" then return v and "true" or "false" end
		if t == "number" then return num(v) end
		if t == "string" then
			if #v <= 48 then return '{"s":"' .. hex(v) .. '"}' end
			local sid = sids[v]
			if sid == nil then
				sid = #slist + 1
				sids[v] = sid
				slist[sid] = v
			end
			return '{"S":' .. sid .. "}"
		end
		if v == env then return '{"env":true}' end
		if (t == "table" or t == "userdata") and gnm[v] ~= nil then return '{"g":"' .. gnm[v] .. '"}' end
		if t == "table" and not isp(v) then
			local id = ids[v]
			if id == nil then
				id = #order + 1
				ids[v] = id
				order[id] = v
			end
			return '{"t":' .. id .. "}"
		end
		if t == "function" then
			if reg[v] ~= nil then
				local up = upv[v]
				if up ~= nil and not ser[v] then
					ser[v] = true
					local es = {}
					for k, x in next, up do es[#es + 1] = '"' .. k .. '":' .. val(x) end
					ser[v] = nil
					return '{"f":"' .. reg[v] .. '","up":{' .. table.concat(es, ",") .. "}}"
				end
				return '{"f":"' .. reg[v] .. '"}'
			end
			if fnm[v] ~= nil then return '{"c":"' .. fnm[v] .. '"}' end
			return '{"c":"?"}'
		end
		if t == "vector" then return '{"v":[' .. num(v.x) .. "," .. num(v.y) .. "," .. num(v.z) .. "]}" end
		if t == "buffer" then return '{"b":"' .. hex(buffer.tostring(v)) .. '"}' end
		local ok, s = pcall(tostring, v)
		return '{"u":"' .. typeof(v) .. '","x":"' .. hex(ok and s or "?") .. '"}'
	end
	local capjs = {}
	for i, c in caps do
		local vars = {}
		for k, v in next, c.vars do vars[#vars + 1] = '"' .. k .. '":' .. val(v) end
		local ps = {}
		for j = 1, math.max(#c.params, 3) do ps[j] = val(c.params[j]) end
		local px = {}
		for j, e in pxs[i] do
			local m = {}
			for k, kv in e[2] do m[k] = "[" .. val(kv[1]) .. "," .. val(kv[2]) .. "]" end
			px[j] = '{"t":' .. val(e[1]) .. ',"map":[' .. table.concat(m, ",") .. "]}"
		end
		capjs[i] = '{"mk":"' .. c.mk .. '"'
			.. (c.order ~= nil and (',"order":' .. c.order) or "")
			.. ',"params":[' .. table.concat(ps, ",") .. '],"vars":{'
			.. table.concat(vars, ",") .. '},"proxies":[' .. table.concat(px, ",") .. "]}"
	end
	for pc, proto in next, pcproto2 do if pcproto[pc] == nil then pcproto[pc] = proto end end
	local pcjs = {}
	for pc, proto in next, pcproto do pcjs[#pcjs + 1] = '"' .. num(pc) .. '":' .. val(proto) end
	local cntjs = {}
	for n, proto in next, cntn do
		if not cntmulti[n] then cntjs[#cntjs + 1] = '"' .. num(n) .. '":' .. val(proto) end
	end
	for n, proto in next, cntn2 do
		if cntn[n] == nil and not cntmulti2[n] then
			cntjs[#cntjs + 1] = '"' .. num(n) .. '":' .. val(proto)
		end
	end
	local skjs = ""
	if mkpc ~= nil then skjs = ',"skip":{"t":' .. val(mkt) .. ',"pc":' .. num(mkpc) .. "}" end
	local tabs = {}
	local i = 1
	while i <= #order do
		local tb = order[i]
		local items = {}
		for k, v in next, tb do items[#items + 1] = "[" .. val(k) .. "," .. val(v) .. "]" end
		local mt = getmetatable(tb)
		tabs[i] = '"' .. i .. '":{"e":[' .. table.concat(items, ",") .. "]"
			.. (mt ~= nil and (',"mt":' .. val(mt)) or "") .. "}"
		i += 1
	end
	local strs = {}
	for k, v in slist do strs[k] = '"' .. hex(v) .. '"' end
	return "\0IBDUMP " .. '{"caps":[' .. table.concat(capjs, ",") .. ']' .. skjs .. ',"pcproto":{' .. table.concat(pcjs, ",")
		.. '},"countproto":{' .. table.concat(cntjs, ",")
		.. '},"tables":{' .. table.concat(tabs, ",")
		.. '},"strings":[' .. table.concat(strs, ",") .. "]}"
end
chn.endHooks = chn.endHooks or {}
table.insert(chn.endHooks, dump)
