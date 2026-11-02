local function fn(n)
	local n2 = n

	return function(n3)
		n2 += n3
		return n2
	end
end

local function fn2()
	return 1
end

local fn3 = fn((fn2()))

local function fn4()
	return 100
end

local fn5 = fn((fn4()))

return function(v)
	return "setup:" .. fn3(v) .. ":" .. fn5(v) .. ":" .. fn3(-1)
end
