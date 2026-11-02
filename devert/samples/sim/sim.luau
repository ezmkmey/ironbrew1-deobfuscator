
local Vec2 = {}
Vec2.__index = Vec2

function Vec2.new(x, y)
	return setmetatable({ x = x, y = y }, Vec2)
end

Vec2.__add = function(a, b)
	return Vec2.new(a.x + b.x, a.y + b.y)
end

Vec2.__sub = function(a, b)
	return Vec2.new(a.x - b.x, a.y - b.y)
end

Vec2.__mul = function(a, k)
	return Vec2.new(a.x * k, a.y * k)
end

Vec2.__eq = function(a, b)
	return a.x == b.x and a.y == b.y
end

Vec2.__tostring = function(v)
	return "(" .. v.x .. "," .. v.y .. ")"
end

function Vec2:manhattan()
	return math.abs(self.x) + math.abs(self.y)
end

local Random = {}
Random.__index = Random

function Random.new(seed)
	return setmetatable({ state = seed % 2147483646 + 1 }, Random)
end

function Random:next()
	self.state = self.state * 48271 % 2147483647
	return self.state
end

function Random:range(low, high)
	return low + self:next() % (high - low + 1)
end

local Heap = {}
Heap.__index = Heap

function Heap.new(before)
	return setmetatable({ items = {}, size = 0, before = before }, Heap)
end

function Heap:push(item)
	self.size += 1
	local items, index = self.items, self.size
	items[index] = item
	while index > 1 do
		local parent = math.floor(index / 2)
		if not self.before(items[index], items[parent]) then
			break
		end
		items[index], items[parent] = items[parent], items[index]
		index = parent
	end
end

function Heap:pop()
	if self.size == 0 then
		return nil
	end
	local items = self.items
	local top, last = items[1], items[self.size]
	items[self.size] = nil
	self.size -= 1
	if self.size == 0 then
		return top
	end
	items[1] = last
	local index = 1
	repeat
		local smallest, left, right = index, index * 2, index * 2 + 1
		if left <= self.size and self.before(items[left], items[smallest]) then
			smallest = left
		end
		if right <= self.size and self.before(items[right], items[smallest]) then
			smallest = right
		end
		if smallest == index then
			break
		end
		items[index], items[smallest] = items[smallest], items[index]
		index = smallest
	until false
	return top
end

local Entity = {}
Entity.__index = Entity

function Entity.new(kind, id, position)
	return setmetatable({ kind = kind, id = id, position = position, notes = {} }, Entity)
end

function Entity:label()
	return self.kind .. "#" .. self.id
end

function Entity:note(time, format, ...)
	local text = format
	if select("#", ...) > 0 then
		text = string.format(format, ...)
	end
	table.insert(self.notes, string.format("%6.2f %s %s", time, self:label(), text))
	return #self.notes
end

local Courier = setmetatable({}, { __index = Entity })
Courier.__index = Courier

function Courier.new(id, position, speed)
	local self = Entity.new("courier", id, position)
	self.speed, self.delivered, self.distance, self.load = speed, 0, 0, 0
	return setmetatable(self, Courier)
end

function Courier:travel(target)
	local leg = (target - self.position):manhattan()
	self.distance += leg
	self.position = target
	return leg / self.speed, leg
end

function Courier:isIdleAt(place)
	return self.load == 0 and self.position == place
end

local function simulate(n)
	local random = Random.new(n * 1009 + 7)
	local depot = Vec2.new(0, 0)
	local queue = Heap.new(function(a, b)
		if a.time ~= b.time then
			return a.time < b.time
		end
		return a.seq < b.seq
	end)
	local sequence = 0
	local function schedule(time, kind, payload)
		sequence += 1
		queue:push({ time = time, seq = sequence, kind = kind, payload = payload })
	end

	local couriers, pending, journal = {}, {}, {}
	for id = 1, 2 + n % 3 do
		couriers[id] = Courier.new(id, depot, 1 + id * 0.5)
	end
	local clock = 0
	for id = 1, 4 + 2 * n do
		clock += random:range(1, 6) / 2
		local target = Vec2.new(random:range(-4, 4), random:range(-4, 4)) * (1 + id % 2)
		schedule(clock, "order", { id = id, target = target, weight = random:range(1, 9) })
	end

	local function dispatch(time)
		for _, courier in ipairs(couriers) do
			if #pending == 0 then
				break
			end
			if not courier:isIdleAt(depot) then
				continue
			end
			local order = table.remove(pending, 1)
			courier.load = order.weight
			if order.target == depot then
				courier:note(time, "hands order %d over at the counter", order.id)
				schedule(time, "deliver", { courier = courier, order = order })
			else
				local duration, leg = courier:travel(order.target)
				courier:note(time, "takes order %d to %s, %d blocks", order.id, tostring(order.target), leg)
				schedule(time + duration, "deliver", { courier = courier, order = order })
			end
		end
	end

	local waiting, longestWait = 0, 0
	while queue.size > 0 do
		local event = queue:pop()
		local time, payload = event.time, event.payload
		if event.kind == "order" then
			payload.placed = time
			table.insert(pending, payload)
			table.sort(pending, function(a, b)
				if a.weight ~= b.weight then
					return a.weight > b.weight
				end
				return a.id < b.id
			end)
		elseif event.kind == "deliver" then
			local courier, order = payload.courier, payload.order
			local wait = time - order.placed
			waiting += wait
			longestWait = math.max(longestWait, wait)
			courier.delivered += 1
			courier.load = 0
			table.insert(journal, string.format("%6.2f order %2d delivered by %s after %.2f", time, order.id, courier:label(), wait))
			local back = courier:travel(depot + Vec2.new(0, 0))
			schedule(time + back, "return", { courier = courier })
		else
			payload.courier:note(time, "back at depot")
		end
		dispatch(time)
	end
	return couriers, journal, waiting, longestWait, clock
end

return function(n)
	local couriers, journal, waiting, longestWait, lastOrder = simulate(n)
	local lines = { string.format("n=%d couriers=%d orders=%d last order at %.1f", n, #couriers, #journal, lastOrder) }
	for index = 1, math.min(#journal, 6) do
		table.insert(lines, journal[index])
	end
	local total, distance = 0, 0
	for _, courier in ipairs(couriers) do
		total += courier.delivered
		distance += courier.distance
		table.insert(lines, string.format("%s speed %.1f delivered %d distance %d at %s, %d notes",
			courier:label(), courier.speed, courier.delivered, courier.distance, tostring(courier.position), #courier.notes))
		for index = #courier.notes, math.max(1, #courier.notes - 1), -1 do
			table.insert(lines, "  " .. courier.notes[index])
		end
	end
	table.insert(lines, string.format("delivered %d, distance %d, mean wait %.3f, longest %.2f", total, distance, waiting / total, longestWait))
	local origin, unit = Vec2.new(0, 0), Vec2.new(1, 1)
	local probe = (unit * n + origin) - unit
	table.insert(lines, string.format("probe %s equals %s: %s", tostring(probe), tostring(unit * (n - 1)), tostring(probe == unit * (n - 1))))
	return table.concat(lines, "\n")
end
