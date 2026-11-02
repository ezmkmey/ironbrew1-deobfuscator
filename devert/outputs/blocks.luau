local n = 0

for i = 1, 4 do
	n += i
end

repeat
	n += 1
until n >= 13

return function(n2)
	return n + n2
end
