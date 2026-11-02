local make = function(initial)
	local total = initial
	return function(step) total += step return total end
end
local left, right = make(1), make(100)
local label = "setup:"
return function(n)
	return label .. left(n) .. ":" .. right(n) .. ":" .. left(-1)
end
