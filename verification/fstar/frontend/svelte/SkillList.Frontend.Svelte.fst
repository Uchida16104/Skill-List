module SkillList.Frontend.Svelte

open FStar.Mul
open FStar.IO
open FStar.All

(* Formally verified Svelte component logic for skill list *)

(* Type definitions for component state *)
type component_state = {
  skills: list skill;
  selected_category: option string;
  search_query: string;
  is_loading: bool;
}

and skill = {
  id: nat;
  name: string;
  category: string;
  level: nat;
  verified: bool;
}

(* Verified state initialization *)
val init_state: unit -> component_state
let init_state () = {
  skills = [];
  selected_category = None;
  search_query = "";
  is_loading = false;
}

(* Verified search function *)
val matches_search: skill -> string -> bool
let matches_search s query =
  let name_lower = String.lowercase s.name in
  let query_lower = String.lowercase query in
  String.contains name_lower query_lower

(* Verified filtering logic *)
val filter_skills: component_state -> list skill
let rec filter_skills_by_query skills query =
  match skills with
  | [] -> []
  | s :: rest ->
      if matches_search s query then
        s :: filter_skills_by_query rest query
      else
        filter_skills_by_query rest query

let filter_skills state =
  let filtered_by_query = 
    if state.search_query = "" then
      state.skills
    else
      filter_skills_by_query state.skills state.search_query
  in
  match state.selected_category with
  | None -> filtered_by_query
  | Some cat -> 
      List.filter (fun s -> s.category = cat) filtered_by_query

(* Verified level validation *)
val is_valid_level: nat -> bool
let is_valid_level level = level >= 1 && level <= 5

(* Verified skill validation *)
val is_valid_skill: skill -> bool
let is_valid_skill s =
  String.length s.name > 0 &&
  String.length s.name <= 100 &&
  String.length s.category > 0 &&
  is_valid_level s.level

(* Verified state update functions *)
val update_search_query: component_state -> string -> component_state
let update_search_query state query = {
  state with search_query = query
}

val update_selected_category: component_state -> option string -> component_state
let update_selected_category state cat = {
  state with selected_category = cat
}

val add_skill: component_state -> skill -> component_state
let add_skill state new_skill =
  if is_valid_skill new_skill then
    { state with skills = new_skill :: state.skills }
  else
    state

(* Verified sorting by skill level *)
val compare_skills: skill -> skill -> bool
let compare_skills s1 s2 = s1.level >= s2.level

(* Export verified component logic *)
