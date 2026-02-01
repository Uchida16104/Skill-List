module SkillList.Frontend.JavaScript

open FStar.Mul
open FStar.IO
open FStar.All

(* Verified JavaScript utility functions for skill list management *)

(* Type definitions for skill data *)
type skill = {
  id: nat;
  name: string;
  category: string;
  verified: bool;
}

type skill_list = list skill

(* Verified function to filter skills by category *)
val filter_by_category: skill_list -> string -> skill_list
let rec filter_by_category skills cat =
  match skills with
  | [] -> []
  | s :: rest ->
      if s.category = cat then
        s :: filter_by_category rest cat
      else
        filter_by_category rest cat

(* Verified function to count verified skills *)
val count_verified: skill_list -> nat
let rec count_verified skills =
  match skills with
  | [] -> 0
  | s :: rest ->
      if s.verified then
        1 + count_verified rest
      else
        count_verified rest

(* Verified function to get skill by ID *)
val get_skill_by_id: skill_list -> nat -> option skill
let rec get_skill_by_id skills target_id =
  match skills with
  | [] -> None
  | s :: rest ->
      if s.id = target_id then
        Some s
      else
        get_skill_by_id rest target_id

(* Verified function to validate skill name *)
val is_valid_skill_name: string -> bool
let is_valid_skill_name name =
  let len = String.length name in
  len > 0 && len <= 100

(* Verified function to sort skills by name *)
val insert_sorted: skill -> skill_list -> skill_list
let rec insert_sorted s skills =
  match skills with
  | [] -> [s]
  | h :: t ->
      if s.name <= h.name then
        s :: skills
      else
        h :: insert_sorted s t

val sort_skills: skill_list -> skill_list
let rec sort_skills skills =
  match skills with
  | [] -> []
  | h :: t -> insert_sorted h (sort_skills t)

(* Export functions for JavaScript compilation *)
(* These will be compiled to JavaScript ES6 modules *)
