# Program Analyser
The Program Analyser is used for experiments in "Static Analysis of Posterior Inference in Bayesian Probabilistic Programming".

## Prerequisite

To use this analyser, install .NET version 6, as it is the version used in this project. The .NET 8.0 also works.

> [Download .NET 6](https://dotnet.microsoft.com/en-us/download/dotnet/6.0)

## Usage

### Using `dotnet`

To run the analyser, ensure the current working directory (`pwd`) is where the `.fsproj` file is located. If not, navigate to the appropriate directory using `cd dotnet runAnalyser` before proceeding.

To execute, use:

> dotnet run <file-path> <option>*

### Building as a Single File

1. To build the analyser as a single file, execute:

> dotnet publish -r <run-time> -p:PublishSingleFile=true --self-contained true

Choose `<run-time>` from the following options:
- For Windows: `win-x64`, `win-x86`, `win-arm`, `win-arm64`.
- For Linux: `linux-x64`, `linux-musl-x64` (Alpine), `linux-arm`, `linux-arm64`.
- For macOS: `osx-x64`, `osx-arm64` (M1 Macs and later).

2. After building, run the file with:

> dotnet run <file-path> <option>*

### Options

- **`-O <output-path>`**: Set the output path. Defaults to the same path as `<program-path>` with a ".txt" extension.
- **`-accuracy <accuracy-number>`** or **`-acc <accuracy-number>`**: Set the accuracy level for end-loop scores. Provide a numeric value.
- **`-termination`**: Use the 'termination' termination type (default setting).
- **`-direct`**: Use the 'direct' termination type.
- **`-concentration`**: Use the 'concentration' termination type.
- **`-truncate`** or **`-truncation`**: Enable truncation in the analysis (enabled by default).
- **`-no-truncation`** or **`-non-truncate`**: Disable truncation.
- **`-R<name>:<min>~<max>`**: Define the range for a variable in the program. Format without spaces.
- **`-m:<number>`**: Specify the division number `m` as described in the paper. Format without spaces.
- **`-degree:<number>`**: Set the degree number `d` as discussed in the paper. Format without spaces.
