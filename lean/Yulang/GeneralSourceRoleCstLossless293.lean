import Yulang.GeneralSourceRoleCstSpan293

/-! A lossless mirror reconstructs bytes, independently of the shell
projection. Bounds are about the supplied token stream, not Rust I/O. -/
set_option maxRecDepth 4096
namespace Yulang.GeneralSourceRoleCstLossless293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstSpan293
open GeneralSourceRoleCstFixture293 (role head block required ws id sigil)

mutual
def render : Tree → String
  | .token _ text => text
  | .node _ children => renderList children
def renderList : List Tree → String
  | [] => ""
  | x::xs => render x ++ renderList xs
end

mutual
theorem render_width (t : Tree) : (render t).utf8ByteSize = width t := by
  cases t with
  | token => rfl
  | node _ cs => exact render_list_width cs
theorem render_list_width (ts : List Tree) : (renderList ts).utf8ByteSize = widths ts := by
  cases ts with
  | nil => rfl
  | cons x xs =>
    rw [renderList,String.utf8ByteSize_append,render_width,render_list_width,widths]
end

def documentedMethod : Tree := .node .binding
  [.token .pubKw "pub", ws, id "index", .token .colon ":", ws,
   .node .head [sigil "'key",ws,.token .other "->",ws,id "value"]]

def documentedRole : Tree := role head (block required documentedMethod)

def documentedFile : Tree := .node .root [documentedRole]

theorem documented_source_exact :
    render documentedFile =
     "pub role Index 'container 'key:\n    type value\n    pub index: 'key -> value" := rfl

theorem documented_extents :
    (locate [0] documentedFile 0).map Prod.snd = some ⟨0,75⟩ ∧
    (locate [0,6] documentedFile 0).map Prod.snd = some ⟨31,75⟩ ∧
    (locate [0,6,1,0] documentedFile 0).map Prod.snd = some ⟨36,46⟩ ∧
    (locate [0,6,3,0] documentedFile 0).map Prod.snd = some ⟨51,75⟩ := by decide

theorem utf8_not_character_offset :
    let tree := Tree.node .root [id "型",documentedRole]
    (locate [1,6,1,0] tree 0).map Prod.snd = some ⟨39,49⟩ := by decide

#guard width documentedFile == 75

end Yulang.GeneralSourceRoleCstLossless293
