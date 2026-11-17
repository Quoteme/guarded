local M = {}
local bin = vim.fn.stdpath("data") .. "/guarded/guarded"
local url = "https://github.com/Quoteme/guarded/releases/download/guarded-lsp/guarded-%s-%s"

local function cmd() return vim.fn.exepath("guarded") ~= "" and "guarded" or bin end

--- Download the language server binary built by GitHub Actions.
function M.install()
  local u = vim.uv.os_uname()
  vim.system({ "curl", "-fsSLo", bin, "--create-dirs", url:format(u.sysname, u.machine) }, {}, function(r)
    vim.schedule(function()
      if r.code ~= 0 then return vim.notify("guarded: download failed\n" .. r.stderr, vim.log.levels.ERROR) end
      vim.uv.fs_chmod(bin, tonumber("755", 8))
      vim.lsp.enable("guarded")
    end)
  end)
end

function M.setup()
  vim.filetype.add({ extension = { grd = "guarded" } })
  vim.lsp.config("guarded", { cmd = { cmd() }, filetypes = { "guarded" }, root_markers = { ".git" } })
  vim.api.nvim_create_user_command("GuardedInstall", M.install, { desc = "Download the guarded LSP" })
  if vim.fn.executable(cmd()) == 1 then vim.lsp.enable("guarded") else M.install() end
end

return M
