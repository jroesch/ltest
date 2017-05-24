structure test_result :=
(test_name : name)
(success : bool)

-- @Kha? can we just build a procedure which auto derives this?
meta instance : has_reflect test_result
| ⟨ n , succ ⟩ := unchecked_cast `(test_result.mk %%(reflect n) %%(reflect succ))

meta instance : has_to_string test_result :=
⟨ fun res, "{ test_name := " ++ to_string res.test_name ++ ", " ++ to_string res.success ++ "}" ⟩

@[user_attribute] def test_result_attr : user_attribute :=
{ name := `test_result, descr := "the result of running a test" }

meta def mk_test_res_decl (res : test_result) : tactic (name × declaration) := do
decl_name ← name.mk_string "_test_result" <$> tactic.mk_fresh_name,
let decl := declaration.defn decl_name [] `(test_result) (reflect res) reducibility_hints.abbrev false,
return (decl_name, decl)

meta def create_test_result (res : test_result) : tactic unit := do
(decl_name, decl) ← mk_test_res_decl res,
tactic.add_decl decl,
tactic.set_basic_attribute `test_result decl_name

meta def mk_list_expr (ty : expr) : list name → tactic expr
| [] := tactic.to_expr ``(@list.nil %%ty)
| (n :: ns) := do
n' ← tactic.mk_const n,
tl ← mk_list_expr ns,
tactic.to_expr ``(%%n' :: %%tl)

meta def collect_test_results : tactic (list test_result) := do
ns ← attribute.get_instances `test_result,
ty ← tactic.to_expr ``(test_result),
ls_expr ← mk_list_expr ty ns,
tactic.eval_expr (list test_result) ls_expr

meta def must_fail (tac : tactic unit) :=
(do tactic.fail_if_success tac,
   create_test_result { test_name := `foo, success := bool.tt },
   tactic.admit) <|> create_test_result { test_name := `foo, success := bool.ff }

def foo : 1 = 1 :=
begin
    create_test_result { test_name := `foo, success := bool.ff },
    reflexivity
end

run_cmd (do rs ← collect_test_results, tactic.trace (to_string rs))
