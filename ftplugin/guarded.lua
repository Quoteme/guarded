vim.bo.commentstring = "-- %s"
for lhs, rhs in pairs({ ["\\later"] = "▷", ["\\->"] = "→", ["\\times"] = "×" }) do
  vim.keymap.set("i", lhs, rhs, { buffer = true, desc = "guarded: insert " .. rhs })
end
