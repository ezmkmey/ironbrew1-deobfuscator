"use strict";
const sglobs = new Set((
  "assert collectgarbage error getfenv getmetatable ipairs load loadstring newproxy next " +
  "pairs pcall print rawequal rawget rawlen rawset require select setfenv setmetatable tonumber tostring type " +
  "typeof unpack xpcall bit32 coroutine debug math os string table utf8 buffer task vector game workspace " +
  "script Enum Instance Vector3 Vector2 CFrame Color3 UDim UDim2 BrickColor Ray Region3 TweenInfo " +
  "NumberRange NumberSequence ColorSequence Random DateTime tick time wait delay spawn warn shared _G " +
  "plugin elapsedTime settings UserSettings Rect Path2DControlPoint Font Axes Faces PhysicalProperties " +
  "Region3int16 Vector3int16 Vector2int16 NumberSequenceKeypoint ColorSequenceKeypoint PathWaypoint " +
  "RaycastParams OverlapParams SharedTable FloatCurveKey RotationCurveKey CatalogSearchParams " +
  "DockWidgetPluginGuiInfo Content gcinfo stats"
).split(/\s+/).filter(Boolean));

module.exports = { sglobs };
