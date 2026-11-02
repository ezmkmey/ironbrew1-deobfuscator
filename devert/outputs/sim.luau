local cls = {}
cls.__index = cls

cls.new = function(x, y)
	return setmetatable({ x = x, y = y }, cls)
end

cls.__add = function(t, t2)
	return cls.new(t.x + t2.x, t.y + t2.y)
end

cls.__sub = function(t, t2)
	return cls.new(t.x - t2.x, t.y - t2.y)
end

cls.__mul = function(t, n)
	return cls.new(t.x * n, t.y * n)
end

cls.__eq = function(t, t2)
	local flag = t.x == t2.x
	if flag then
		return t.y == t2.y
	end
	return flag
end

cls.__tostring = function(t)
	return "(" .. t.x .. "," .. t.y .. ")"
end

cls.manhattan = function(self)
	return math.abs(self.x) + math.abs(self.y)
end

local cls2 = {}
cls2.__index = cls2

cls2.new = function(n)
	return setmetatable({ state = n % 2147483646 + 1 }, cls2)
end

cls2.next = function(self)
	self.state = self.state * 48271 % 2147483647
	return self.state
end

cls2.range = function(self, n, n2)
	return n + self:next() % (n2 - n + 1)
end

local cls3 = {}
cls3.__index = cls3

cls3.new = function(before)
	local t = { items = {} }
	t.size = 0
	t.before = before
	return setmetatable(t, cls3)
end

cls3.push = function(self, t)
	self.size += 1
	local items = self.items
	local size = self.size
	items[size] = t

	while size > 1 do
		local n = math.floor(size / 2)

		if not self.before(items[size], items[n]) then
			break
		else
			local item = items[n]
			local item2 = items[size]
			items[size] = item
			items[n] = item2
			size = n
		end
	end
end

cls3.pop = function(self)
	if self.size == 0 then
		return nil
	end
	local items = self.items
	local item = items[1]
	local item2 = items[self.size]
	items[self.size] = nil
	self.size -= 1
	if self.size == 0 then
		return item
	end
	items[1] = item2
	local n = 1
	local n2

	while true do
		n2 = n
		local n3 = n * 2
		local n4 = n * 2 + 1

		if (n3 <= self.size and self.before(items[n3], items[n2])) then
			n2 = n3
		end

		if (n4 <= self.size and self.before(items[n4], items[n2])) then
			n2 = n4
		end

		if n2 == n then
			break
		else
			local item3 = items[n2]
			local item4 = items[n]
			items[n] = item3
			items[n2] = item4
			n = n2
		end
	end

	return item
end

local cls4 = {}
cls4.__index = cls4

cls4.new = function(kind, id, pos)
	local t = { kind = kind, id = id }
	t.position = pos
	t.notes = {}
	return setmetatable(t, cls4)
end

cls4.label = function(self)
	return self.kind .. "#" .. self.id
end

cls4.note = function(self, tm, fmt, ...)
	local s = fmt

	if select("#", ...) > 0 then
		s = string.format(fmt, ...)
	end

	table.insert(self.notes, string.format("%6.2f %s %s", tm, self:label(), s))
	return #self.notes
end

local cls5 = setmetatable({}, { __index = cls4 })
cls5.__index = cls5

cls5.new = function(id, pos, speed)
	local obj = cls4.new("courier", id, pos)
	obj.speed = speed
	obj.delivered = 0
	obj.distance = 0
	obj.load = 0
	return setmetatable(obj, cls5)
end

cls5.travel = function(self, pos)
	local n = (pos - self.position):manhattan()
	self.distance += n
	self.position = pos
	return n / self.speed, n
end

cls5.isIdleAt = function(self, t)
	return self.load == 0 and self.position == t
end

local function fn(n)
	local obj = cls2.new(n * 1009 + 7)
	local obj2 = cls.new(0, 0)
	local new = cls3.new

	local obj3 = new(function(t, t2)
		if t.time == t2.time then
			return t.seq < t2.seq
		end
		return t.time < t2.time
	end)

	local seq = 0

	local function fn2(tm, kind, payload)
		seq += 1
		obj3.push(obj3, { time = tm, seq = seq, kind = kind, payload = payload })
	end

	local couriers = {}
	local orders = {}
	local t = {}

	for i = 1, 2 + n % 3 do
		couriers[i] = cls5.new(i, obj2, 1 + i * 0.5)
	end

	local tm = 0

	for i = 1, 4 + 2 * n do
		tm += obj:range(1, 6) / 2
		local tgt = cls.new(obj:range(-4, 4), obj:range(-4, 4)) * (1 + i % 2)
		fn2(tm, "order", { id = i, target = tgt, weight = obj:range(1, 9) })
	end

	local function fn3(tm2)
		local kind = "deliver"

		for _, courier in ipairs(couriers) do
			if #orders == 0 then
				break
			elseif not courier:isIdleAt(obj2) then
			else
				local order = table.remove(orders, 1)
				courier.load = order.weight

				if order.target == obj2 then
					courier.note(courier, tm2, "hands order %d over at the counter", order.id)
					fn2(tm2, kind, { courier = courier, order = order })
				else
					local n2, n3 = courier.travel(courier, order.target)
					courier.note(courier, tm2, "takes order %d to %s, %d blocks",
						order.id, tostring(order.target), n3)
					fn2(tm2 + n2, kind, { courier = courier, order = order })
				end
			end
		end
	end

	local sum = 0
	local max = 0

	while obj3.size > 0 do
		local item = obj3:pop()
		local tm2 = item.time
		local payload = item.payload

		if item.kind == "order" then
			payload.placed = tm2
			table.insert(orders, payload)

			table.sort(orders, function(a, b)
				if not (a.weight == b.weight) then
					return a.weight > b.weight
				end
				return a.id < b.id
			end)
		elseif item.kind == "deliver" then
			local courier = payload.courier
			local order = payload.order
			local n2 = tm2 - order.placed
			sum += n2
			max = math.max(max, n2)
			courier.delivered += 1
			courier.load = 0
			table.insert(t, string.format("%6.2f order %2d delivered by %s after %.2f",
				tm2, order.id, courier:label(), n2))
			local n3 = courier.travel(courier, obj2 + cls.new(0, 0))
			fn2(tm2 + n3, "return", { courier = courier })
		else
			payload.courier:note(tm2, "back at depot")
		end

		fn3(tm2)
	end

	return couriers, t, sum, max, tm
end

return function(n)
	local couriers, t, n2, n3, n4 = fn(n)

	local buf = {
		string.format("n=%d couriers=%d orders=%d last order at %.1f", n, #couriers, #t, n4),
	}

	for i = 1, math.min(#t, 6) do
		table.insert(buf, t[i])
	end

	local sum = 0
	local dist = 0

	for _, courier in ipairs(couriers) do
		sum += courier.delivered
		dist += courier.distance
		table.insert(buf,
			string.format("%s speed %.1f delivered %d distance %d at %s, %d notes", courier:label(),
			courier.speed, courier.delivered, courier.distance,
			tostring(courier.position), #courier.notes))

		for i = #courier.notes, math.max(1, #courier.notes - 1), -1 do
			table.insert(buf, "  " .. courier.notes[i])
		end
	end

	table.insert(buf, string.format("delivered %d, distance %d, mean wait %.3f, longest %.2f",
		sum, dist, n2 / sum, n3))
	local obj = cls.new(0, 0)
	local obj2 = cls.new(1, 1)
	local n5 = obj2 * n + obj - obj2
	table.insert(buf, string.format("probe %s equals %s: %s", tostring(n5),
		tostring(obj2 * (n - 1)), tostring(n5 == obj2 * (n - 1))))
	return table.concat(buf, "\n")
end
