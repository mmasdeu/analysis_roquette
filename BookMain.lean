import VersoManual
import Book

open Verso.Genre Manual

/-- Configuration of the companion's HTML output. -/
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc Book) (config := config)
