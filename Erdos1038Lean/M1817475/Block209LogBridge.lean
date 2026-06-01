import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block209

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block209

open Set

def block209W1 : Rat := ((4834284345859217 : Rat) / 5000000000000000)
def block209W2 : Rat := ((5286623331704121 : Rat) / 100000000000000000)
def block209W3 : Rat := ((2193440782636243 : Rat) / 12500000000000000)
def block209W4 : Rat := ((9725175059546629 : Rat) / 100000000000000000)
def block209S1 : Rat := ((18174751 : Rat) / 10000000)
def block209S2 : Rat := ((511587 : Rat) / 200000)
def block209S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block209S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block209V (y : ℝ) : ℝ :=
  ratPotential block209W1 block209W2 block209W3 block209W4 block209S1 block209S2 block209S3 block209S4 y

def block209LeftParamsCertificate : Bool :=
  allBoxesSameParams block209LeftBoxes block209W1 block209W2 block209W3 block209W4 block209S1 block209S2 block209S3 block209S4

theorem block209LeftParamsCertificate_eq_true :
    block209LeftParamsCertificate = true := by
  native_decide

theorem block209_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block209LeftL : ℝ) (block209LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block209S1 : ℝ))
    (hy2ne : y ≠ (block209S2 : ℝ))
    (hy3ne : y ≠ (block209S3 : ℝ))
    (hy4ne : y ≠ (block209S4 : ℝ)) :
    0 < block209V y := by
  have hcert := block209LeftCertificate_eq_true
  unfold block209LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block209LeftBoxes) (lo := block209LeftL) (hi := block209LeftR)
    (w1 := block209W1) (w2 := block209W2) (w3 := block209W3) (w4 := block209W4)
    (s1 := block209S1) (s2 := block209S2) (s3 := block209S3) (s4 := block209S4)
    hboxes hcover block209LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block209RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block209RightChunk000 block209W1 block209W2 block209W3 block209W4 block209S1 block209S2 block209S3 block209S4

theorem block209RightChunk000ParamsCertificate_eq_true :
    block209RightChunk000ParamsCertificate = true := by
  native_decide

theorem block209_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block209RightChunk000L : ℝ) (block209RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block209S1 : ℝ))
    (hy2ne : y ≠ (block209S2 : ℝ))
    (hy3ne : y ≠ (block209S3 : ℝ))
    (hy4ne : y ≠ (block209S4 : ℝ)) :
    0 < block209V y := by
  have hcert := block209RightChunk000Certificate_eq_true
  unfold block209RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block209RightChunk000) (lo := block209RightChunk000L) (hi := block209RightChunk000R)
    (w1 := block209W1) (w2 := block209W2) (w3 := block209W3) (w4 := block209W4)
    (s1 := block209S1) (s2 := block209S2) (s3 := block209S3) (s4 := block209S4)
    hboxes hcover block209RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block209RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block209RightChunk001 block209W1 block209W2 block209W3 block209W4 block209S1 block209S2 block209S3 block209S4

theorem block209RightChunk001ParamsCertificate_eq_true :
    block209RightChunk001ParamsCertificate = true := by
  native_decide

theorem block209_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block209RightChunk001L : ℝ) (block209RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block209S1 : ℝ))
    (hy2ne : y ≠ (block209S2 : ℝ))
    (hy3ne : y ≠ (block209S3 : ℝ))
    (hy4ne : y ≠ (block209S4 : ℝ)) :
    0 < block209V y := by
  have hcert := block209RightChunk001Certificate_eq_true
  unfold block209RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block209RightChunk001) (lo := block209RightChunk001L) (hi := block209RightChunk001R)
    (w1 := block209W1) (w2 := block209W2) (w3 := block209W3) (w4 := block209W4)
    (s1 := block209S1) (s2 := block209S2) (s3 := block209S3) (s4 := block209S4)
    hboxes hcover block209RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block209RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block209RightChunk002 block209W1 block209W2 block209W3 block209W4 block209S1 block209S2 block209S3 block209S4

theorem block209RightChunk002ParamsCertificate_eq_true :
    block209RightChunk002ParamsCertificate = true := by
  native_decide

theorem block209_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block209RightChunk002L : ℝ) (block209RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block209S1 : ℝ))
    (hy2ne : y ≠ (block209S2 : ℝ))
    (hy3ne : y ≠ (block209S3 : ℝ))
    (hy4ne : y ≠ (block209S4 : ℝ)) :
    0 < block209V y := by
  have hcert := block209RightChunk002Certificate_eq_true
  unfold block209RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block209RightChunk002) (lo := block209RightChunk002L) (hi := block209RightChunk002R)
    (w1 := block209W1) (w2 := block209W2) (w3 := block209W3) (w4 := block209W4)
    (s1 := block209S1) (s2 := block209S2) (s3 := block209S3) (s4 := block209S4)
    hboxes hcover block209RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block209RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block209RightChunk003 block209W1 block209W2 block209W3 block209W4 block209S1 block209S2 block209S3 block209S4

theorem block209RightChunk003ParamsCertificate_eq_true :
    block209RightChunk003ParamsCertificate = true := by
  native_decide

theorem block209_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block209RightChunk003L : ℝ) (block209RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block209S1 : ℝ))
    (hy2ne : y ≠ (block209S2 : ℝ))
    (hy3ne : y ≠ (block209S3 : ℝ))
    (hy4ne : y ≠ (block209S4 : ℝ)) :
    0 < block209V y := by
  have hcert := block209RightChunk003Certificate_eq_true
  unfold block209RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block209RightChunk003) (lo := block209RightChunk003L) (hi := block209RightChunk003R)
    (w1 := block209W1) (w2 := block209W2) (w3 := block209W3) (w4 := block209W4)
    (s1 := block209S1) (s2 := block209S2) (s3 := block209S3) (s4 := block209S4)
    hboxes hcover block209RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block209_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block209RightL : ℝ) (block209RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block209S1 : ℝ))
    (hy2ne : y ≠ (block209S2 : ℝ))
    (hy3ne : y ≠ (block209S3 : ℝ))
    (hy4ne : y ≠ (block209S4 : ℝ)) :
    0 < block209V y := by
  by_cases h0 : y ≤ (block209RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block209RightChunk000L : ℝ) (block209RightChunk000R : ℝ) := by
      have hL : (block209RightChunk000L : ℝ) = (block209RightL : ℝ) := by
        norm_num [block209RightChunk000L, block209RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block209_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block209RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block209RightChunk001L : ℝ) (block209RightChunk001R : ℝ) := by
        have hprev : (block209RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block209RightChunk001L : ℝ) = (block209RightChunk000R : ℝ) := by
          norm_num [block209RightChunk001L, block209RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block209_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block209RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block209RightChunk002L : ℝ) (block209RightChunk002R : ℝ) := by
          have hprev : (block209RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block209RightChunk002L : ℝ) = (block209RightChunk001R : ℝ) := by
            norm_num [block209RightChunk002L, block209RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block209_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        have hprev : (block209RightChunk002R : ℝ) < y := lt_of_not_ge h2
        have hL : (block209RightChunk003L : ℝ) = (block209RightChunk002R : ℝ) := by
          norm_num [block209RightChunk003L, block209RightChunk002R]
        have hR : (block209RightChunk003R : ℝ) = (block209RightR : ℝ) := by
          norm_num [block209RightChunk003R, block209RightR]
        have hyc : y ∈ Icc (block209RightChunk003L : ℝ) (block209RightChunk003R : ℝ) := by
          constructor
          · linarith [hprev, hL]
          · linarith [hy.2, hR]
        exact block209_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block209_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block209LeftL : ℝ) (block209LeftR : ℝ) →
    y ≠ 0 → y ≠ (block209S1 : ℝ) → y ≠ (block209S2 : ℝ) →
    y ≠ (block209S3 : ℝ) → y ≠ (block209S4 : ℝ) → 0 < block209V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block209RightL : ℝ) (block209RightR : ℝ) →
    y ≠ 0 → y ≠ (block209S1 : ℝ) → y ≠ (block209S2 : ℝ) →
    y ≠ (block209S3 : ℝ) → y ≠ (block209S4 : ℝ) → 0 < block209V y)

theorem block209_reallog_certificate_proof :
    block209_reallog_certificate := by
  exact ⟨block209_left_V_pos, block209_right_V_pos⟩

end Block209
end M1817475
end Erdos1038Lean
