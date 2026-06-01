import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block167

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block167

open Set

def block167W1 : Rat := ((9175536484583483 : Rat) / 5000000000000000)
def block167W2 : Rat := (0 : Rat)
def block167W3 : Rat := ((16578470619419997 : Rat) / 100000000000000000)
def block167W4 : Rat := ((5128500783163451 : Rat) / 50000000000000000)
def block167S1 : Rat := ((18174751 : Rat) / 10000000)
def block167S2 : Rat := ((511587 : Rat) / 200000)
def block167S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block167S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block167V (y : ℝ) : ℝ :=
  ratPotential block167W1 block167W2 block167W3 block167W4 block167S1 block167S2 block167S3 block167S4 y

def block167LeftParamsCertificate : Bool :=
  allBoxesSameParams block167LeftBoxes block167W1 block167W2 block167W3 block167W4 block167S1 block167S2 block167S3 block167S4

theorem block167LeftParamsCertificate_eq_true :
    block167LeftParamsCertificate = true := by
  native_decide

theorem block167_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block167LeftL : ℝ) (block167LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block167S1 : ℝ))
    (hy2ne : y ≠ (block167S2 : ℝ))
    (hy3ne : y ≠ (block167S3 : ℝ))
    (hy4ne : y ≠ (block167S4 : ℝ)) :
    0 < block167V y := by
  have hcert := block167LeftCertificate_eq_true
  unfold block167LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block167LeftBoxes) (lo := block167LeftL) (hi := block167LeftR)
    (w1 := block167W1) (w2 := block167W2) (w3 := block167W3) (w4 := block167W4)
    (s1 := block167S1) (s2 := block167S2) (s3 := block167S3) (s4 := block167S4)
    hboxes hcover block167LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block167RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block167RightChunk000 block167W1 block167W2 block167W3 block167W4 block167S1 block167S2 block167S3 block167S4

theorem block167RightChunk000ParamsCertificate_eq_true :
    block167RightChunk000ParamsCertificate = true := by
  native_decide

theorem block167_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block167RightChunk000L : ℝ) (block167RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block167S1 : ℝ))
    (hy2ne : y ≠ (block167S2 : ℝ))
    (hy3ne : y ≠ (block167S3 : ℝ))
    (hy4ne : y ≠ (block167S4 : ℝ)) :
    0 < block167V y := by
  have hcert := block167RightChunk000Certificate_eq_true
  unfold block167RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block167RightChunk000) (lo := block167RightChunk000L) (hi := block167RightChunk000R)
    (w1 := block167W1) (w2 := block167W2) (w3 := block167W3) (w4 := block167W4)
    (s1 := block167S1) (s2 := block167S2) (s3 := block167S3) (s4 := block167S4)
    hboxes hcover block167RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block167_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block167RightL : ℝ) (block167RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block167S1 : ℝ))
    (hy2ne : y ≠ (block167S2 : ℝ))
    (hy3ne : y ≠ (block167S3 : ℝ))
    (hy4ne : y ≠ (block167S4 : ℝ)) :
    0 < block167V y := by
  have hL : (block167RightChunk000L : ℝ) = (block167RightL : ℝ) := by
    norm_num [block167RightChunk000L, block167RightL]
  have hR : (block167RightChunk000R : ℝ) = (block167RightR : ℝ) := by
    norm_num [block167RightChunk000R, block167RightR]
  have hyc : y ∈ Icc (block167RightChunk000L : ℝ) (block167RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block167_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block167_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block167LeftL : ℝ) (block167LeftR : ℝ) →
    y ≠ 0 → y ≠ (block167S1 : ℝ) → y ≠ (block167S2 : ℝ) →
    y ≠ (block167S3 : ℝ) → y ≠ (block167S4 : ℝ) → 0 < block167V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block167RightL : ℝ) (block167RightR : ℝ) →
    y ≠ 0 → y ≠ (block167S1 : ℝ) → y ≠ (block167S2 : ℝ) →
    y ≠ (block167S3 : ℝ) → y ≠ (block167S4 : ℝ) → 0 < block167V y)

theorem block167_reallog_certificate_proof :
    block167_reallog_certificate := by
  exact ⟨block167_left_V_pos, block167_right_V_pos⟩

end Block167
end M1817475
end Erdos1038Lean
