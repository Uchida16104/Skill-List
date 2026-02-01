module SkillList.Backend.Network.Rust

open FStar.Mul
open FStar.IO
open FStar.All

(* Formally verified network handling for Rust backend *)

type ip_address = string
type port_number = n:nat{n > 0 && n <= 65535}
type request_method = GET | POST | PUT | DELETE
type response_status = OK | Created | BadRequest | NotFound | InternalError

type network_request = {
  method: request_method;
  path: string;
  headers: list (string * string);
  body: string;
}

type network_response = {
  status: response_status;
  headers: list (string * string);
  body: string;
}

val is_valid_path: string -> bool
let is_valid_path path =
  String.length path > 0 && String.starts_with path "/"

val status_to_code: response_status -> nat
let status_to_code status =
  match status with
  | OK -> 200
  | Created -> 201
  | BadRequest -> 400
  | NotFound -> 404
  | InternalError -> 500

val create_response: response_status -> string -> network_response
let create_response status body = {
  status = status;
  headers = [("Content-Type", "application/json")];
  body = body;
}

val create_json_response: response_status -> string -> network_response
let create_json_response status json_body = {
  status = status;
  headers = [("Content-Type", "application/json"); ("Access-Control-Allow-Origin", "*")];
  body = json_body;
}

val validate_request: network_request -> bool
let validate_request req =
  is_valid_path req.path

(* Export verified network functions *)
