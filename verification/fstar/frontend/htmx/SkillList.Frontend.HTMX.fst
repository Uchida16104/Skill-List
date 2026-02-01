module SkillList.Frontend.HTMX

open FStar.Mul
open FStar.IO
open FStar.All

(* Formally verified HTMX attribute generation and interaction patterns *)

(* Type definitions for HTMX attributes *)
type http_method = GET | POST | PUT | DELETE | PATCH
type trigger_event = Click | Change | Submit | Load | Revealed

type htmx_attributes = {
  method: http_method;
  url: string;
  target: string;
  swap: string;
  trigger: trigger_event;
}

(* Verified URL validation *)
val is_valid_url: string -> bool
let is_valid_url url =
  let len = String.length url in
  len > 0 && len < 2000 && (
    String.starts_with url "/" ||
    String.starts_with url "http://" ||
    String.starts_with url "https://"
  )

(* Verified method to string conversion *)
val method_to_string: http_method -> string
let method_to_string m =
  match m with
  | GET -> "get" | POST -> "post" | PUT -> "put" 
  | DELETE -> "delete" | PATCH -> "patch"

(* Verified trigger to string conversion *)
val trigger_to_string: trigger_event -> string
let trigger_to_string t =
  match t with
  | Click -> "click" | Change -> "change" | Submit -> "submit"
  | Load -> "load" | Revealed -> "revealed"

(* Verified HTMX attribute generation *)
val generate_hx_get: string -> string -> string
let generate_hx_get url target =
  if is_valid_url url then
    "hx-get=\"" ^ url ^ "\" hx-target=\"" ^ target ^ "\""
  else
    ""

val generate_hx_post: string -> string -> string
let generate_hx_post url target =
  if is_valid_url url then
    "hx-post=\"" ^ url ^ "\" hx-target=\"" ^ target ^ "\""
  else
    ""

(* Verified swap strategy generation *)
type swap_strategy = InnerHTML | OuterHTML | BeforeBegin | AfterBegin | BeforeEnd | AfterEnd

val swap_to_string: swap_strategy -> string
let swap_to_string s =
  match s with
  | InnerHTML -> "innerHTML"
  | OuterHTML -> "outerHTML"
  | BeforeBegin -> "beforebegin"
  | AfterBegin -> "afterbegin"
  | BeforeEnd -> "beforeend"
  | AfterEnd -> "afterend"

val generate_hx_swap: swap_strategy -> string
let generate_hx_swap strategy =
  "hx-swap=\"" ^ swap_to_string strategy ^ "\""

(* Verified skill list HTMX patterns *)
val generate_skill_load_attributes: unit -> string
let generate_skill_load_attributes () =
  generate_hx_get "/api/skills" "#skill-list" ^ " " ^ generate_hx_swap InnerHTML

val generate_skill_search_attributes: unit -> string
let generate_skill_search_attributes () =
  "hx-get=\"/api/skills/search\" hx-trigger=\"keyup changed delay:300ms\" hx-target=\"#skill-list\""

val generate_skill_delete_attributes: nat -> string
let generate_skill_delete_attributes id =
  let url = "/api/skills/" ^ string_of_int id in
  "hx-delete=\"" ^ url ^ "\" hx-confirm=\"Are you sure?\" hx-target=\"closest .skill-card\" hx-swap=\"outerHTML\""

(* Verified form submission attributes *)
val generate_skill_form_attributes: unit -> string
let generate_skill_form_attributes () =
  "hx-post=\"/api/skills\" hx-target=\"#skill-list\" hx-swap=\"beforeend\""

(* Export verified HTMX utilities *)
