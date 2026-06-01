import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block513

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block513

open Set

def block513W1 : Rat := ((133780050629521 : Rat) / 312500000000000)
def block513W2 : Rat := (0 : Rat)
def block513W3 : Rat := ((885782333440697 : Rat) / 2000000000000000)
def block513W4 : Rat := ((4423382374235979 : Rat) / 2000000000000000000)
def block513S1 : Rat := ((18174751 : Rat) / 10000000)
def block513S2 : Rat := ((511587 : Rat) / 200000)
def block513S3 : Rat := ((130104865267857143017 : Rat) / 50000000000000000000)
def block513S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block513V (y : ℝ) : ℝ :=
  ratPotential block513W1 block513W2 block513W3 block513W4 block513S1 block513S2 block513S3 block513S4 y

def block513LeftParamsCertificate : Bool :=
  allBoxesSameParams block513LeftBoxes block513W1 block513W2 block513W3 block513W4 block513S1 block513S2 block513S3 block513S4

theorem block513LeftParamsCertificate_eq_true :
    block513LeftParamsCertificate = true := by
  native_decide

theorem block513_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block513LeftL : ℝ) (block513LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block513S1 : ℝ))
    (hy2ne : y ≠ (block513S2 : ℝ))
    (hy3ne : y ≠ (block513S3 : ℝ))
    (hy4ne : y ≠ (block513S4 : ℝ)) :
    0 < block513V y := by
  have hcert := block513LeftCertificate_eq_true
  unfold block513LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block513LeftBoxes) (lo := block513LeftL) (hi := block513LeftR)
    (w1 := block513W1) (w2 := block513W2) (w3 := block513W3) (w4 := block513W4)
    (s1 := block513S1) (s2 := block513S2) (s3 := block513S3) (s4 := block513S4)
    hboxes hcover block513LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block513RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block513RightChunk000 block513W1 block513W2 block513W3 block513W4 block513S1 block513S2 block513S3 block513S4

theorem block513RightChunk000ParamsCertificate_eq_true :
    block513RightChunk000ParamsCertificate = true := by
  native_decide

theorem block513_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block513RightChunk000L : ℝ) (block513RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block513S1 : ℝ))
    (hy2ne : y ≠ (block513S2 : ℝ))
    (hy3ne : y ≠ (block513S3 : ℝ))
    (hy4ne : y ≠ (block513S4 : ℝ)) :
    0 < block513V y := by
  have hcert := block513RightChunk000Certificate_eq_true
  unfold block513RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block513RightChunk000) (lo := block513RightChunk000L) (hi := block513RightChunk000R)
    (w1 := block513W1) (w2 := block513W2) (w3 := block513W3) (w4 := block513W4)
    (s1 := block513S1) (s2 := block513S2) (s3 := block513S3) (s4 := block513S4)
    hboxes hcover block513RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block513_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block513RightL : ℝ) (block513RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block513S1 : ℝ))
    (hy2ne : y ≠ (block513S2 : ℝ))
    (hy3ne : y ≠ (block513S3 : ℝ))
    (hy4ne : y ≠ (block513S4 : ℝ)) :
    0 < block513V y := by
  have hL : (block513RightChunk000L : ℝ) = (block513RightL : ℝ) := by
    norm_num [block513RightChunk000L, block513RightL]
  have hR : (block513RightChunk000R : ℝ) = (block513RightR : ℝ) := by
    norm_num [block513RightChunk000R, block513RightR]
  have hyc : y ∈ Icc (block513RightChunk000L : ℝ) (block513RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block513_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block513_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block513LeftL : ℝ) (block513LeftR : ℝ) →
    y ≠ 0 → y ≠ (block513S1 : ℝ) → y ≠ (block513S2 : ℝ) →
    y ≠ (block513S3 : ℝ) → y ≠ (block513S4 : ℝ) → 0 < block513V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block513RightL : ℝ) (block513RightR : ℝ) →
    y ≠ 0 → y ≠ (block513S1 : ℝ) → y ≠ (block513S2 : ℝ) →
    y ≠ (block513S3 : ℝ) → y ≠ (block513S4 : ℝ) → 0 < block513V y)

theorem block513_reallog_certificate_proof :
    block513_reallog_certificate := by
  exact ⟨block513_left_V_pos, block513_right_V_pos⟩

end Block513
end M1817475
end Erdos1038Lean
