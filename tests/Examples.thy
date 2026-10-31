theory Examples
  imports "../src/Frontend"
begin

definition cascade :: "nat instruction list" where
  "cascade = [Jump 127, Jump 130] @ replicate 128 Nop @ [Stop]"

definition countdown :: "nat instruction list" where
  "countdown = [Inc, Inc, Inc, Dec, Zero 6, Jump 3, Stop]"

definition forward :: "nat \<Rightarrow> nat instruction list" where
  "forward n = [Jump (Suc n)] @ replicate n Nop @ [Stop]"

definition backward :: "nat \<Rightarrow> nat instruction list" where
  "backward n = replicate n Nop @ [Jump 0, Stop]"

lemma cascade_rounds:
  "map (\<lambda>W. filter (\<lambda>i. i \<in> W) [0..<length cascade]) (history cascade {}) = [[], [1], [0,1]]"
  by eval

lemma cascade_size: "map_option length (assemble cascade) = Some 135"
  by eval

lemma forward_short: "layout (forward 127) = {}"
  by eval

lemma forward_long: "layout (forward 128) = {0}"
  by eval

lemma backward_short: "layout (backward 126) = {}"
  by eval

lemma backward_long: "layout (backward 127) = {127}"
  by eval

lemma countdown_execution:
  "execute (source_step countdown) 32 (0,0) = (6,0)"
  by eval

lemma countdown_bytes:
  "assemble countdown = Some [1,1,1,2,17,130,16,123,3]"
  by eval

lemma short_negative_boundary:
  "decode [16,0] = Some (Branch False False (-128), [])"
  by eval

lemma long_negative_boundary:
  "decode [18,0,0] = Some (Branch False True (-32768), [])"
  by eval

lemma long_positive_boundary:
  "decode [18,255,255] = Some (Branch False True 32767, [])"
  by eval

lemma truncated_rejected: "decode [18,1] = None"
  by eval

lemma unknown_rejected: "decode [255] = None"
  by eval

lemma short_payload_rejected: "decode [16,256] = None"
  by eval

lemma long_payload_rejected: "decode [19,0,256] = None"
  by eval

lemma decoder_preserves_tail:
  "decode [19,255,255,3,255] = Some (Branch True True 32767, [3,255])"
  by eval

lemma undefined_rejected:
  "compile ''jmp missing'' = Error ''undefined label missing''"
  by eval

lemma duplicate_rejected:
  "compile (''label a'' @ newline @ ''label a'') = Error ''duplicate label a''"
  by eval

lemma final_label_rejected:
  "compile (''jmp end'' @ newline @ ''label end'') = Error ''branch targets a label after the final instruction''"
  by eval

end
