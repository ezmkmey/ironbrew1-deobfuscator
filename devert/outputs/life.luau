local cls = {}
cls.__index = cls

cls.new = function(width, height)
	local cells = {}

	for i = 1, width * height do
		cells[i] = false
	end

	return setmetatable({ width = width, height = height, cells = cells }, cls)
end

cls.index = function(self, x, y)
	return (y - 1) % self.height * self.width + (x - 1) % self.width + 1
end

cls.get = function(self, x, y)
	return self.cells[self:index(x, y)]
end

cls.set = function(self, x, y, flag)
	self.cells[self:index(x, y)] = flag
end

cls.__eq = function(t, t2)
	if not (t.width ~= t2.width) then
		if not (t.height ~= t2.height) then
			for i, cell in ipairs(t.cells) do
				if t2.cells[i] == cell then
				else
					return false
				end
			end

			return true
		end
	end

	return false
end

cls.neighbours = function(self, x, y)
	local cnt = 0

	for i = -1, 1 do
		for j = -1, 1 do
			if ((j ~= 0 or i ~= 0) and self:get(x + j, y + i)) then
				cnt += 1
			end
		end
	end

	return cnt
end

cls.step = function(self, t)
	local obj = cls.new(self.width, self.height)
	local cnt = 0
	local cnt2 = 0
	local flag

	for y = 1, self.height do
		for x = 1, self.width do
			local cell = self:get(x, y)
			local n = self:neighbours(x, y)
			flag = false

			if cell then
				flag = t.survive[n] == true

				if not flag then
					cnt2 += 1
				end
			elseif t.born[n] then
				flag = true
				cnt += 1
			end

			obj:set(x, y, flag)
		end
	end

	return obj, cnt, cnt2
end

cls.population = function(self)
	local cnt = 0

	for _, cell in ipairs(self.cells) do
		if cell then
			cnt += 1
		end
	end

	return cnt
end

cls.render = function(self)
	local buf = {}

	for y = 1, self.height do
		local buf2 = {}

		for x = 1, self.width do
			local s = (self:get(x, y) and "#") or "."
			buf2[x] = s
		end

		buf[y] = table.concat(buf2)
	end

	return table.concat(buf, "\n")
end

local function fn(obj, y)
	for x = 1, obj.width do
		if obj:get(x, y) then
			return true
		end
	end

	return false
end

local function fn2(obj, x)
	for y = 1, obj.height do
		if obj:get(x, y) then
			return true
		end
	end

	return false
end

cls.boundingBox = function(self)
	local n, n2, n3, n4

	for y = 1, self.height do
		if fn(self, y) then
			n = y
			break
		end
	end

	if n == nil then
		return nil
	end

	for y = self.height, n, -1 do
		if fn(self, y) then
			n2 = y
			break
		end
	end

	for x = 1, self.width do
		if fn2(self, x) then
			n3 = x
			break
		end
	end

	for x = self.width, n3, -1 do
		if fn2(self, x) then
			n4 = x
			break
		end
	end

	return n, n2, n3, n4
end

local function fn3(s)
	local s2, s3 = string.match(s, "^B(%d*)/S(%d*)$")

	if s2 == nil then
		error({ rule = s, reason = "expected B<digits>/S<digits>" }, 0)
	end

	local t = { name = s, born = {}, survive = {} }

	for i = 1, #s2 do
		t.born[string.byte(s2, i) - 48] = true
	end

	for s4 in string.gmatch(s3, "%d") do
		t.survive[tonumber(s4)] = true
	end

	return t
end

local t = {
	glider = ".#.|..#|###",
	blinker = "###",
	toad = ".###|###.",
	rpentomino = ".##|##.|.#.",
	block = "##|##",
	domino = "##",
}

local function fn4(obj, v, x, y0)
	local y = y0
	local cnt = 0

	for s in string.gmatch(t[v] .. "|", "([^|]*)|") do
		for i = 1, #s do
			if string.sub(s, i, i) == "#" then
				obj.set(obj, x + i - 1, y, true)
				cnt += 1
			end
		end

		y += 1
	end

	return cnt
end

local t2 = {
	{ "B3/S23", { "blinker" } },
	{ "B36/S23", { "rpentomino" } },
	{ "B3/S23", { "toad", "block", "glider" } },
	{ "B2/S", { "blinker" } },
	{ "B3/S12345", { "rpentomino", "block" } },
	{ "B3S23", { "glider" } },
	{ "B3/S23", { "domino", "glider" } },
	{ "B3/S23", { "domino" } },
}

local function fn5(n, t3)
	local ok, res = pcall(fn3, t3[1])
	if not ok then
		return { string.format("rule %s rejected: %s", res.rule, res.reason) }
	end
	local obj = cls.new(10, 8)
	local sum = 0

	for i, v in ipairs(t3[2]) do
		local x = 1 + (i * 3 + n) % 8
		local y = 1 + (i * 2 + n) % 6
		sum += fn4(obj, v, x, y)
	end

	local t4 = { string.format("rule %s, %d cells placed", res.name, sum) }
	local buf = { obj:population() }
	local t5 = { [obj:render()] = 0 }
	local births = 0
	local deaths = 0

	for i = 1, n + 3 do
		local t6, n2, n3 = obj:step(res)
		births += n2
		deaths += n3

		if t6 == obj then
			table.insert(t4, string.format("still life after %d generations", i - 1))
			break
		else
			obj = t6
			table.insert(buf, t6:population())
			local s = obj:render()

			if t5[s] == nil then
				t5[s] = i
			else
				table.insert(t4, string.format("cycle of period %d at generation %d", i - t5[s], i))
				break
			end
		end
	end

	table.insert(t4,
		string.format("population %s; births %d deaths %d", table.concat(buf, " "), births, deaths))
	local n4, n5, n6, n7 = obj:boundingBox()

	if n4 == nil then
		table.insert(t4, "extinct")
	else
		table.insert(t4, string.format("box rows %d-%d columns %d-%d", n4, n5, n6, n7))
		table.insert(t4, obj:render())
	end

	return t4
end

return function(n)
	local buf = {}
	local t3 = { 0, 3 }

	for _, n2 in ipairs(t3) do
		local t4 = t2[(n + n2 - 1) % #t2 + 1]

		for _, v in ipairs(fn5(n, t4)) do
			table.insert(buf, v)
		end
	end

	return table.concat(buf, "\n")
end
