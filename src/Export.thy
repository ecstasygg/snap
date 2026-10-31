theory Export
  imports Frontend
begin

definition ascii :: "integer \<Rightarrow> char" where "ascii = char_of"

definition ordinal :: "char \<Rightarrow> integer" where "ordinal = of_char"

export_code process binary artifact disassemble ascii ordinal in SML module_name Span file_prefix span

end
