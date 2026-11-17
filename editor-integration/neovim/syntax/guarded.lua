if vim.b.current_syntax then return end
vim.cmd([[
  syn match guardedDef "^[[:alpha:]_][[:alnum:]_']*"
  syn match guardedType "\<\u[[:alnum:]_']*"
  syn keyword guardedKeyword later next match
  syn match guardedCommand "^#\w\+"
  syn match guardedNumber "\<[01]\>"
  syn match guardedOperator ":=\|->\|[→×▷+*|]"
  syn match guardedComment "\(--\|//\).*$" contains=@Spell
]])
for group, link in pairs({ Def = "Function", Type = "Type", Keyword = "Keyword", Command = "PreProc",
  Number = "Number", Operator = "Operator", Comment = "Comment" }) do
  vim.api.nvim_set_hl(0, "guarded" .. group, { link = link, default = true })
end
vim.b.current_syntax = "guarded"
