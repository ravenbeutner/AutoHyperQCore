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

module AutoHyperQCore.RunConfiguration 

open System
open System.IO

open Util
open FsOmegaLib.JSON 


type SolverConfiguration = 
    {
        MainPath : Option<String>
        AutfiltPath: Option<String>
        Ltl2tgbaPath: Option<String>
    }

    member this.GetMainPath = 
        this.MainPath
        |> Option.defaultWith (fun _ -> raise <| AnalysisException "Requested main path, but this was not defined")
    
    member this.GetAutfiltPath = 
        this.AutfiltPath
        |> Option.defaultWith (fun _ -> raise <| AnalysisException "Requested autfilt path, but this was not defined")

    member this.GetLtl2tgbaPath = 
        this.Ltl2tgbaPath
        |> Option.defaultWith (fun _ -> raise <| AnalysisException "Requested ltl2tgba path, but this was not defined")


let private parseConfigFile (s : string) =
    match FsOmegaLib.JSON.Parser.parseJsonString s with 
    | Result.Error err -> raise <| AnalysisException $"Could not parse config file: %s{err}"
    | Result.Ok x -> 
        {
            MainPath = "./" |> Some
            AutfiltPath =
                (JSON.tryLookup "autfilt" x)
                |> Option.bind (fun x -> JSON.tryGetString x)
            Ltl2tgbaPath = 
                (JSON.tryLookup "ltl2tgba" x)
                |> Option.bind (fun x -> JSON.tryGetString x)
        }

let getConfig() = 
    // By convention the paths.json file is located in the same directory as the HyPA executable
    let configPath = 
        System.IO.Path.Join [|System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location); "paths.json"|]
                     
    // Check if the path to the config file is valid , i.e., the file exists
    if System.IO.FileInfo(configPath).Exists |> not then 
        raise <| AnalysisException "The paths.json file does not exist in the same directory as the executable"            
    
    // Parse the config File
    let configContent = 
        try
            File.ReadAllText configPath
        with 
            | _ -> 
                raise <| AnalysisException "Could not open paths.json file"

    let solverConfig = parseConfigFile configContent

    if solverConfig.AutfiltPath.IsSome then 
        if System.IO.FileInfo(solverConfig.AutfiltPath.Value).Exists |> not then 
            raise <| AnalysisException "The given path to the spot's autfilt is incorrect"

    if solverConfig.Ltl2tgbaPath.IsSome then 
        if System.IO.FileInfo(solverConfig.Ltl2tgbaPath.Value).Exists |> not then 
            raise <| AnalysisException "The given path to the spot's ltl2tgba is incorrect"

    solverConfig