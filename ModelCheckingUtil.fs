(*    
    Copyright (C) 2022-2023 Raven Beutner

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module AutoHyperQCore.ModelCheckingUtil

open System

open FsOmegaLib.GNBA

open Util
open HyperQPTL


exception private NotWellFormedException of String

let findErrorOnMcInstance (tsList: GNBA<int,'L> list) (formula: HyperQPTL<'L>)  = 
    try 
        match HyperQPTL.findError formula with 
        | None -> ()
        | Some msg -> 
            raise <| NotWellFormedException $"Error in the specification: %s{msg}"
        
        tsList
        |> List.iteri (fun i x ->
            match GNBA.findError x with 
            | None -> () 
            | Some msg -> 
                raise <| NotWellFormedException $"Error in the %i{i}th transition system: %s{msg}"
            )

        let traceVarList =
            HyperQPTL.quantifiedTraceVariables formula

        if tsList.Length <> traceVarList.Length && tsList.Length <> 1 then 
            raise <| NotWellFormedException "Invalid number of systems"
              
        formula.LTLMatrix
        |> FsOmegaLib.LTL.LTL.allAtoms
        |> Set.iter (fun x ->
            match x with
            | TraceAtom (a, pi) ->
                if List.contains pi traceVarList |> not then 
                    raise <| AnalysisException $"No System defined for trace variable %s{pi}"
                
                if tsList.Length = 1 then 
                    if List.contains a tsList.[0].APs |> not then
                        raise <| AnalysisException $"AP (%A{a}, %s{pi}) is used in the HyperQPTL formula, but AP %A{a} is not defined in the system for %s{pi}."
                else 
                    let index = List.findIndex ((=) pi) traceVarList
                    if List.contains a tsList.[index].APs |> not then
                        raise <| AnalysisException $"AP (%A{a}, %s{pi}) is used in the HyperQPTL formula, but AP %A{a} is not defined in the system for %s{pi}."
            | PropAtom _ -> ()
        )

        None 
    with 
    | NotWellFormedException msg -> Some msg
    