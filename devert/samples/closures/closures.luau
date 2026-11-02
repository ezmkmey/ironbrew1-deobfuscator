return function(n)
	local total = 3
	local function bump(x)
		total = total + x
		return total
	end
	local methods = {}
	methods.run = function(x) return bump(x) * 2 end
	local function choose(x)
		local f = methods.run
		if x % 2 == 0 then f = function(y) return bump(y) - 1 end end
		return f(x)
	end
	local function recurse(x)
		if x == 0 then return total end
		return choose(x) + recurse(x - 1)
	end
	local first = recurse(n)
	methods.run = function(x) return bump(-x) end
	return tostring(first) .. ":" .. tostring(methods.run(n)) .. ":" .. tostring(total)
end
