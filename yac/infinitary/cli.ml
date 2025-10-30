open Formula
open Deduction

type state =
  | PromptContext
  | PromptFormula
  | PromptProof

type msg =
  | GiveFormula of formula

type model = {
    context : formula list;
    state : state
  }

let prompt_formula () =
  print_endline "Choose constructor or enter 'help' to display help message";
  print_string "> ";
  let rec aux () =
    match read_line() with
    | "Leq" ->
    | "Le" ->
    | "Eq" ->
    |
  in
  aux()

let view model =
  match model.state with
  | PromptContext -> _
  | PromptFormula -> _
  | PromptProof -> _

let update model = _

let rec loop model =
  let msg = view model in
  let model' = update model msg in
  loop model'
