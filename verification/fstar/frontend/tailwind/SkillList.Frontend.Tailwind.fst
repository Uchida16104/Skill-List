module SkillList.Frontend.Tailwind

open FStar.Mul
open FStar.IO
open FStar.All

(* Formally verified Tailwind CSS utility class generation *)

(* Type definitions for Tailwind utilities *)
type spacing_scale = 
  | S0 | S1 | S2 | S3 | S4 | S5 | S6 | S8 | S10 | S12 | S16 | S20 | S24

type color_intensity = 
  | I50 | I100 | I200 | I300 | I400 | I500 | I600 | I700 | I800 | I900

type tailwind_class = string

(* Verified spacing to numeric value conversion *)
val spacing_to_value: spacing_scale -> nat
let spacing_to_value s =
  match s with
  | S0 -> 0 | S1 -> 4 | S2 -> 8 | S3 -> 12 | S4 -> 16
  | S5 -> 20 | S6 -> 24 | S8 -> 32 | S10 -> 40 | S12 -> 48
  | S16 -> 64 | S20 -> 80 | S24 -> 96

(* Verified utility class generation *)
val generate_padding_class: spacing_scale -> tailwind_class
let generate_padding_class s =
  match s with
  | S0 -> "p-0" | S1 -> "p-1" | S2 -> "p-2" | S3 -> "p-3" | S4 -> "p-4"
  | S5 -> "p-5" | S6 -> "p-6" | S8 -> "p-8" | S10 -> "p-10" | S12 -> "p-12"
  | S16 -> "p-16" | S20 -> "p-20" | S24 -> "p-24"

val generate_margin_class: spacing_scale -> tailwind_class
let generate_margin_class s =
  match s with
  | S0 -> "m-0" | S1 -> "m-1" | S2 -> "m-2" | S3 -> "m-3" | S4 -> "m-4"
  | S5 -> "m-5" | S6 -> "m-6" | S8 -> "m-8" | S10 -> "m-10" | S12 -> "m-12"
  | S16 -> "m-16" | S20 -> "m-20" | S24 -> "m-24"

(* Verified color class generation *)
val generate_bg_color_class: string -> color_intensity -> tailwind_class
let generate_bg_color_class color intensity =
  let intensity_str = match intensity with
    | I50 -> "50" | I100 -> "100" | I200 -> "200" | I300 -> "300" | I400 -> "400"
    | I500 -> "500" | I600 -> "600" | I700 -> "700" | I800 -> "800" | I900 -> "900"
  in
  "bg-" ^ color ^ "-" ^ intensity_str

val generate_text_color_class: string -> color_intensity -> tailwind_class
let generate_text_color_class color intensity =
  let intensity_str = match intensity with
    | I50 -> "50" | I100 -> "100" | I200 -> "200" | I300 -> "300" | I400 -> "400"
    | I500 -> "500" | I600 -> "600" | I700 -> "700" | I800 -> "800" | I900 -> "900"
  in
  "text-" ^ color ^ "-" ^ intensity_str

(* Verified responsive class generation *)
type breakpoint = SM | MD | LG | XL | XXL

val generate_responsive_class: breakpoint -> tailwind_class -> tailwind_class
let generate_responsive_class bp base_class =
  let prefix = match bp with
    | SM -> "sm:" | MD -> "md:" | LG -> "lg:" | XL -> "xl:" | XXL -> "2xl:"
  in
  prefix ^ base_class

(* Verified class combination *)
val combine_classes: list tailwind_class -> tailwind_class
let rec combine_classes classes =
  match classes with
  | [] -> ""
  | [c] -> c
  | c :: rest -> c ^ " " ^ combine_classes rest

(* Verified skill card utility classes *)
val generate_skill_card_classes: bool -> tailwind_class
let generate_skill_card_classes is_verified =
  let base = ["rounded-lg"; "shadow-md"; "p-4"; "m-2"; "border"] in
  let border_class = if is_verified then "border-green-500" else "border-gray-300" in
  combine_classes (base @ [border_class])

(* Export verified Tailwind utilities *)
