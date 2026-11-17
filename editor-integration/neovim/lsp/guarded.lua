-- prefer `guarded` on $PATH, else the binary bundled by CI in bin/
local u = vim.uv.os_uname()
local bundled = vim.api.nvim_get_runtime_file(("bin/guarded-%s-%s"):format(u.sysname, u.machine), false)[1]
return {
  cmd = { vim.fn.exepath("guarded") ~= "" and "guarded" or bundled or "guarded" },
  filetypes = { "guarded" },
  root_markers = { ".git" },
}
