
local Grid = {}
Grid.__index = Grid

function Grid.new(width, height)
	local cells = {}
	for index = 1, width * height do
		cells[index] = false
	end
	return setmetatable({ width = width, height = height, cells = cells }, Grid)
end

function Grid:index(x, y)
	return ((y - 1) % self.height) * self.width + (x - 1) % self.width + 1
end

function Grid:get(x, y)
	return self.cells[self:index(x, y)]
end

function Grid:set(x, y, alive)
	self.cells[self:index(x, y)] = alive
end

Grid.__eq = function(a, b)
	if a.width ~= b.width or a.height ~= b.height then
		return false
	end
	for index, alive in ipairs(a.cells) do
		if b.cells[index] ~= alive then
			return false
		end
	end
	return true
end

function Grid:neighbours(x, y)
	local count = 0
	for dy = -1, 1 do
		for dx = -1, 1 do
			if (dx ~= 0 or dy ~= 0) and self:get(x + dx, y + dy) then
				count += 1
			end
		end
	end
	return count
end

function Grid:step(rule)
	local nextGrid = Grid.new(self.width, self.height)
	local births, deaths = 0, 0
	for y = 1, self.height do
		for x = 1, self.width do
			local alive, count = self:get(x, y), self:neighbours(x, y)
			local lives = false
			if alive then
				lives = rule.survive[count] == true
				if not lives then
					deaths += 1
				end
			elseif rule.born[count] then
				lives = true
				births += 1
			end
			nextGrid:set(x, y, lives)
		end
	end
	return nextGrid, births, deaths
end

function Grid:population()
	local count = 0
	for _, alive in ipairs(self.cells) do
		if alive then
			count += 1
		end
	end
	return count
end

function Grid:render()
	local rows = {}
	for y = 1, self.height do
		local row = {}
		for x = 1, self.width do
			row[x] = self:get(x, y) and "#" or "."
		end
		rows[y] = table.concat(row)
	end
	return table.concat(rows, "\n")
end

local function rowHasLife(grid, y)
	for x = 1, grid.width do
		if grid:get(x, y) then
			return true
		end
	end
	return false
end

local function columnHasLife(grid, x)
	for y = 1, grid.height do
		if grid:get(x, y) then
			return true
		end
	end
	return false
end

function Grid:boundingBox()
	local top, bottom, left, right = nil, nil, nil, nil
	for y = 1, self.height do
		if rowHasLife(self, y) then
			top = y
			break
		end
	end
	if top == nil then
		return nil
	end
	for y = self.height, top, -1 do
		if rowHasLife(self, y) then
			bottom = y
			break
		end
	end
	for x = 1, self.width do
		if columnHasLife(self, x) then
			left = x
			break
		end
	end
	for x = self.width, left, -1 do
		if columnHasLife(self, x) then
			right = x
			break
		end
	end
	return top, bottom, left, right
end

local function parseRule(text)
	local born, survive = string.match(text, "^B(%d*)/S(%d*)$")
	if born == nil then
		error({ rule = text, reason = "expected B<digits>/S<digits>" }, 0)
	end
	local rule = { name = text, born = {}, survive = {} }
	for index = 1, #born do
		rule.born[string.byte(born, index) - 48] = true
	end
	for digit in string.gmatch(survive, "%d") do
		rule.survive[tonumber(digit)] = true
	end
	return rule
end

local PATTERNS = {
	glider = ".#.|..#|###",
	blinker = "###",
	toad = ".###|###.",
	rpentomino = ".##|##.|.#.",
	block = "##|##",
	domino = "##",
}

local function stamp(grid, pattern, originX, originY)
	local y = originY
	local placed = 0
	for row in string.gmatch(PATTERNS[pattern] .. "|", "([^|]*)|") do
		for x = 1, #row do
			if string.sub(row, x, x) == "#" then
				grid:set(originX + x - 1, y, true)
				placed += 1
			end
		end
		y += 1
	end
	return placed
end

local SCENARIOS = {
	{ "B3/S23", { "blinker" } },
	{ "B36/S23", { "rpentomino" } },
	{ "B3/S23", { "toad", "block", "glider" } },
	{ "B2/S", { "blinker" } },
	{ "B3/S12345", { "rpentomino", "block" } },
	{ "B3S23", { "glider" } },
	{ "B3/S23", { "domino", "glider" } },
	{ "B3/S23", { "domino" } },
}

local function run(n, scenario)
	local ok, rule = pcall(parseRule, scenario[1])
	if not ok then
		return { string.format("rule %s rejected: %s", rule.rule, rule.reason) }
	end
	local grid = Grid.new(10, 8)
	local placed = 0
	for index, pattern in ipairs(scenario[2]) do
		placed += stamp(grid, pattern, 1 + (index * 3 + n) % 8, 1 + (index * 2 + n) % 6)
	end
	local lines = { string.format("rule %s, %d cells placed", rule.name, placed) }
	local history, seen = { grid:population() }, { [grid:render()] = 0 }
	local totalBirths, totalDeaths = 0, 0
	for generation = 1, n + 3 do
		local nextGrid, births, deaths = grid:step(rule)
		totalBirths += births
		totalDeaths += deaths
		if nextGrid == grid then
			table.insert(lines, string.format("still life after %d generations", generation - 1))
			break
		end
		grid = nextGrid
		table.insert(history, grid:population())
		local picture = grid:render()
		if seen[picture] ~= nil then
			table.insert(lines, string.format("cycle of period %d at generation %d", generation - seen[picture], generation))
			break
		end
		seen[picture] = generation
	end
	table.insert(lines, string.format("population %s; births %d deaths %d", table.concat(history, " "), totalBirths, totalDeaths))
	local top, bottom, left, right = grid:boundingBox()
	if top == nil then
		table.insert(lines, "extinct")
	else
		table.insert(lines, string.format("box rows %d-%d columns %d-%d", top, bottom, left, right))
		table.insert(lines, grid:render())
	end
	return lines
end

return function(n)
	local output = {}
	for _, offset in ipairs({ 0, 3 }) do
		local scenario = SCENARIOS[(n + offset - 1) % #SCENARIOS + 1]
		for _, line in ipairs(run(n, scenario)) do
			table.insert(output, line)
		end
	end
	return table.concat(output, "\n")
end
