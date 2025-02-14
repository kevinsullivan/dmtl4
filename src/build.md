# Getting Started

The DMTL4 book is largely generated from Lean 4 source. You can experiment with
all of the examples in the VS Code IDE. First, follow the [Lean 4 quickstart][1] to
install VS Code, Lean, and the Lean 4 extension. Second, [install `git`][2] and
clone your fork of the repository. Next, open the repository in VS code.
Finally, open the notes you wish to run. The book's Lean code can be found in the
`code/DMT1/Lectures/` directory.

## Building DMTL4

If you wish to generate the book yourself there are additional steps and
dependencies you will need.

First, install [`mdbook`][4].  

Additionally, install [`mdbook-toc`][7], [`mdbook-mermaid`][8] and
[`mdbook-image-size`][9]. To do so, download the appropriate tarball for you
system architecture and unpack it into a directory on your path.

Then, install the Haskell installer, [`ghcup`][5].  

Add `ghcup`'s bin directory (`$HOME/.ghcup/bin`) to your `PATH`.  

Next, launch the TUI and install `ghcup`'s recommend Haskell version.  

Lastly, if not already installed, install `make` on your platform.

At this point you should be able to build the book. From the top-level
directory run `make all`. This will transform the code (in `code/DMT`) into
markdown (in `src/DMT1`) for the book.

Finally, you can serve up the book for browsing with `mdbook serve --open &`.
Conveniently, any changes to the `src` directory will cause the book to be
rebuilt automatically.

### Install Scripts

Manual installation instructions will be replaced with automated install
scripts over time. We welcome any and all contributions to this effort.

### Windows

Not available at this time.

### macOS

The dependencies described above can be installed on macOS via [homebrew][6] with the
following commands.

```bash
brew install mdbook ghcup

# Assuming x86_64. Tweak for apple silicon.
curl -L https://github.com/badboy/mdbook-mermaid/releases/download/v0.14.1/mdbook
-mermaid-v0.14.1-x86_64-apple-darwin.tar.gz | tar -xz -C $HOME/.local/bin
curl -L https://github.com/badboy/mdbook-toc/releases/download/0.14.2/mdbook-toc-0.14.2-x86_64-apple-darwin.tar.gz | tar -xz -C $HOME/.local/bin

# Assuming bash. Tweak if using a different shell.
echo 'PATH=$PATH:$HOME/.ghcup/bin' >> "$HOME/.bashrc"

ghcup install ghc recommended
ghcup set ghc recommended
```

## Other

Note, Windows users using git via [git bash][3] and the command line should take
care to select the appropriate shell in the VS Code terminal. It will do to
set git bash as the terminal by changing Settings: Terminal > Integrated >
Defafult Profile: Windows and selecting it there. Thereafter, launching a
terminal in VS Code will launch one with a git bash shell. You can see what's
possible there in the configuration section and eventually configure your own
setup for terminal in VS Code.  

Note, rust users can install the mdbook extensions with cargo.

[1]: https://lean-lang.org/lean4/doc/quickstart.html
[2]: https://github.com/git-guides/install-git
[3]: https://gitforwindows.org
[4]: https://github.com/rust-lang/mdBook/releases/tag/v0.4.43
[5]: https://www.haskell.org/ghcup/
[6]: https://brew.sh
[7]: https://github.com/badboy/mdbook-toc/releases/tag/0.14.2
[8]: https://github.com/badboy/mdbook-mermaid/releases/tag/v0.14.1
[9]: https://github.com/lhybdv/mdbook-image-size/releases/tag/0.2.0
