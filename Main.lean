import FleanBlogPost.Page
import FleanBlogPost.Post

def main (_ : List String) := renderPage (%doc FleanBlogPost.Post)

/-
def basicSite : Site := site DemoSite.Front /
  static "static" ← "static_files"
  "about" DemoSite.About
  "blog" DemoSite.Blog with
    DemoSite.Blog.Subprojects
    DemoSite.Blog.Conditionals
    DemoSite.Blog.FirstPost



def main := blogMain theme demoSite


def main :=
  blogMain (%doc Manual) (config := config)
where
  config := addKaTeX {
    extraFiles := [("static", "static")],
    extraCss := [
      "/static/colors.css",
      "/static/theme.css",
      "/static/print.css",
      "/static/search/search-box.css",
      "/static/fonts/source-serif/source-serif-text.css",
      "/static/fonts/source-code-pro/source-code-pro.css",
      "/static/fonts/source-sans/source-sans-3.css",
    ],
    extraJs := [
      -- Search box
      "/static/search/fuzzysort.js",
      -- Print stylesheet improvements
      "/static/print.js"
    ],
    extraHead := #[searchModule],
    emitTeX := false,
    emitHtmlSingle := true, -- for proofreading
    logo := some "/static/lean_logo.svg",
    sourceLink := some "https://github.com/leanprover/reference-manual",
    issueLink := some "https://github.com/leanprover/reference-manual/issues"
    -- Licenses for the search box
    licenseInfo := [fuzzysortLicense, w3ComboboxLicense]
  }
-/
