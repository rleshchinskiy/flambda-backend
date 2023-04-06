(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Fabrice Le Fessant, INRIA Saclay                     *)
(*                                                                        *)
(*   Copyright 2012 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Misc

type pers_flags =
  | Rectypes
  | Alerts of alerts
  | Opaque
  | Unsafe_string

type error =
  | Not_an_interface of filepath
  | Wrong_version_interface of filepath * string
  | Corrupted_interface of filepath

exception Error of error

(* these type abbreviations are not exported;
   they are used to provide consistency across
   input_value and output_value usage. *)
(* type signature = Types.signature_item list *)

type crcs = Import_info.t array  (* smaller on disk than using a list *)
type flags = pers_flags list

module Serialized = Types.Make(struct type 'a t = int end)

type header = Compilation_unit.t * Serialized.signature

type cmi_infos = {
  cmi_name : Compilation_unit.t;
  cmi_sign : Subst.Lazy.signature;
  cmi_crcs : Import_info.t array;
  cmi_flags : pers_flags list;
}

module Deserialize = Types.Map_pods(Serialized)(Subst.Lazy)

let deserialize data =
  let map_signature fn n =
    lazy(
      Marshal.from_bytes data n
      |> List.map (Deserialize.signature_item fn))
    |> Subst.Lazy.of_lazy_signature_items
  in
  let map_type_expr _ n =
    lazy(Marshal.from_bytes data n : Types.type_expr) |> Subst.Lazy.of_lazy
  in
  Deserialize.signature {map_signature; map_type_expr}

module Serialize = Types.Map_pods(Subst.Lazy)(Serialized)

let serialize oc base =
  let marshal x =
    let pos = Out_channel.pos oc in
    Marshal.to_channel oc x [];
    Int64.to_int pos - base
  in
  let map_signature fn sg =
    Subst.Lazy.force_signature_once sg
    |> List.map (Serialize.signature_item fn)
    |> marshal
  in
  let map_type_expr _ ty = Subst.Lazy.force_type_expr ty |> marshal in
  Serialize.signature {map_signature; map_type_expr}
    
let input_cmi ic =
  let read_bytes n =
    let buf = Bytes.create n in
    match In_channel.really_input ic buf 0 n with
    | Some () -> buf
    | None -> assert false
  in
  let data_len = Bytes.get_int64_ne (read_bytes 8) 0 |> Int64.to_int in
  let data = read_bytes data_len in
  let (name, sign) = (input_value ic : header) in
  let crcs = (input_value ic : crcs) in
  let flags = (input_value ic : flags) in
  {
    cmi_name = name;
    cmi_sign = deserialize data sign;
    cmi_crcs = crcs;
    cmi_flags = flags;
  }

let read_cmi filename =
  let ic = open_in_bin filename in
  try
    let buffer =
      really_input_string ic (String.length Config.cmi_magic_number)
    in
    if buffer <> Config.cmi_magic_number then begin
      close_in ic;
      let pre_len = String.length Config.cmi_magic_number - 3 in
      if String.sub buffer 0 pre_len
          = String.sub Config.cmi_magic_number 0 pre_len then
      begin
        let msg =
          if buffer < Config.cmi_magic_number then "an older" else "a newer" in
        raise (Error (Wrong_version_interface (filename, msg)))
      end else begin
        raise(Error(Not_an_interface filename))
      end
    end;
    let cmi = input_cmi ic in
    close_in ic;
    cmi
  with End_of_file | Failure _ ->
      close_in ic;
      raise(Error(Corrupted_interface(filename)))
    | Error e ->
      close_in ic;
      raise (Error e)

let output_cmi filename oc cmi =
(* beware: the provided signature must have been substituted for saving *)
  output_string oc Config.cmi_magic_number;
  let output_int64 oc n =
    let buf = Bytes.create 8 in
    Bytes.set_int64_ne buf 0 n;
    output_bytes oc buf
  in
  let len_pos = Out_channel.pos oc in
  output_int64 oc Int64.zero;
  let data_pos = Int64.to_int len_pos + 8 in
  let sign = serialize oc data_pos cmi.cmi_sign in
  let val_pos = Out_channel.pos oc in
  Out_channel.seek oc len_pos;
  let len = Int64.sub val_pos (Int64.of_int data_pos) in
  output_int64 oc len;
  Out_channel.seek oc val_pos;
  output_value oc ((cmi.cmi_name, sign) : header);
  flush oc;
  let crc = Digest.file filename in
  let crcs =
    Array.append [| Import_info.create_normal cmi.cmi_name ~crc:(Some crc) |]
      cmi.cmi_crcs
  in
  output_value oc (crcs : crcs);
  output_value oc (cmi.cmi_flags : flags);
  crc

(* Error report *)

open Format

let report_error ppf = function
  | Not_an_interface filename ->
      fprintf ppf "%a@ is not a compiled interface"
        Location.print_filename filename
  | Wrong_version_interface (filename, older_newer) ->
      fprintf ppf
        "%a@ is not a compiled interface for this version of OCaml.@.\
         It seems to be for %s version of OCaml."
        Location.print_filename filename older_newer
  | Corrupted_interface filename ->
      fprintf ppf "Corrupted compiled interface@ %a"
        Location.print_filename filename

let () =
  Location.register_error_of_exn
    (function
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
