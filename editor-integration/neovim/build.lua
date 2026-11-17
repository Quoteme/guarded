-- run by lazy.nvim on install/update: unpack this platform's server binary
local dir = vim.fs.dirname(debug.getinfo(1, "S").source:sub(2))
local u = vim.uv.os_uname()
local r = vim.system({ "xz", "-dkf", ("%s/bin/guarded-%s-%s.xz"):format(dir, u.sysname, u.machine) }):wait()
assert(r.code == 0, "guarded: " .. r.stderr)
