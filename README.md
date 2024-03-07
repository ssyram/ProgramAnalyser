# ProgramAnalyser
The program analyser for the experiments in "Static Analysis of Posterior Inference in Bayesian Probabilistic Programming".

## Prerequisite

Install .NET, the version used in this project is .NET 6.

> https://dotnet.microsoft.com/en-us/download/dotnet/6.0

## Usage 

### Use `dotnet`
Assume `pwd` is in the directory with the `.fsproj` file, that is, 
use `cd ./ProgramAnalyser` first when the terminal is at the current directory:

> dotnet run <file-path> < option >*

### Build in A Single File

1. Build a single file by:

> dotnet publish -r <run-time> -p:PublishSingleFile=true --self-contained true

where the `<run-time>` could be:
- Windows: win-x64, win-x86, win-arm, win-arm64.
- Linux: linux-x64, linux-musl-x64 (for Alpine), linux-arm, linux-arm64.
- macOS: osx-x64, osx-arm64 (for M1 Macs and later).

2. Run the file:

> ./program <file-path> < option >*

### Options:

- **`<file-path>`** : The path to the `.program` file. This is a required parameter.

- **`-O <output-path>`** : Specify the output path. Otherwise it will be the same as the `<program-path>` with extension changing to ".txt".

- **`-accuracy <accuracy-number>`** or **`-acc <accuracy-number>`** : Set the desired accuracy level for end-loop scores with a numeric value.

- **`-termination`** : Use the 'termination' termination type. This is the default.

- **`-direct`** : Use the 'direct' termination type.

- **`-concentration`** : Use the 'concentration' termination type.

- **`-truncate`** or **`-truncation`** : Enables truncation in the analysis (enabled by default).

- **`-no-truncation`** or **`-non-truncate`** : Run the analysis without truncation.

- **`-R<name>:<min>~<max>`**: Specify the range of a given variable in the program (no space).

- **`-m:<number>`**: Specify the division number `m` as in the paper (no space).

- **`-degree:<number>`**: Specify the degree number `d` as in the paper (no space).

## Default Example Configurations

```
dotnet run ./h-t-r-2-3.program
dotnet run ./h-t-r-2-3-inside-score.program
dotnet run ./growing-walk-Q1.program -direct -acc 1e-4 -no-truncate
dotnet run ./para-estimation-recursive.program -direct -acc 1e-5 -no-truncate
dotnet run ./pedestrian-multiple-branches-v5.program -direct -acc 1e-4
dotnet run ./pedestrian-multiple-branches-v4.program -direct -acc 1e-4
dotnet run ./add-uniform-unbounded-Q1.program -direct -no-truncate
dotnet run ./cav-example-5-Q2.program -direct -no-truncate
dotnet run ./cav-example-7-Q1.program -direct -no-truncate
dotnet run ./pedestrian.program -direct -acc 1e-4 -no-truncate
dotnet run ./pedestrian-deviation5.program -direct -acc 1e-4
dotnet run ./random-box-walk-Q1.program -direct -no-truncate
dotnet run ./random-walk-beta-inside-scorey-v4.program -terminate
```
