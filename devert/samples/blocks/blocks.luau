do
	local total = 0
	for i = 1, 4 do total = total + i end
	repeat total = total + 1 until total >= 13
	return function(n) return total + n end
end
