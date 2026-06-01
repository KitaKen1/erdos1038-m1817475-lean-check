import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block195

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block195

open Set

def block195W1 : Rat := ((17352254841346089 : Rat) / 10000000000000000)
def block195W2 : Rat := (0 : Rat)
def block195W3 : Rat := ((2279166822326623 : Rat) / 12500000000000000)
def block195W4 : Rat := ((9089979426386881 : Rat) / 100000000000000000)
def block195S1 : Rat := ((18174751 : Rat) / 10000000)
def block195S2 : Rat := ((511587 : Rat) / 200000)
def block195S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block195S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block195V (y : ℝ) : ℝ :=
  ratPotential block195W1 block195W2 block195W3 block195W4 block195S1 block195S2 block195S3 block195S4 y

def block195LeftParamsCertificate : Bool :=
  allBoxesSameParams block195LeftBoxes block195W1 block195W2 block195W3 block195W4 block195S1 block195S2 block195S3 block195S4

theorem block195LeftParamsCertificate_eq_true :
    block195LeftParamsCertificate = true := by
  native_decide

theorem block195_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block195LeftL : ℝ) (block195LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block195S1 : ℝ))
    (hy2ne : y ≠ (block195S2 : ℝ))
    (hy3ne : y ≠ (block195S3 : ℝ))
    (hy4ne : y ≠ (block195S4 : ℝ)) :
    0 < block195V y := by
  have hcert := block195LeftCertificate_eq_true
  unfold block195LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block195LeftBoxes) (lo := block195LeftL) (hi := block195LeftR)
    (w1 := block195W1) (w2 := block195W2) (w3 := block195W3) (w4 := block195W4)
    (s1 := block195S1) (s2 := block195S2) (s3 := block195S3) (s4 := block195S4)
    hboxes hcover block195LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block195RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block195RightChunk000 block195W1 block195W2 block195W3 block195W4 block195S1 block195S2 block195S3 block195S4

theorem block195RightChunk000ParamsCertificate_eq_true :
    block195RightChunk000ParamsCertificate = true := by
  native_decide

theorem block195_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block195RightChunk000L : ℝ) (block195RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block195S1 : ℝ))
    (hy2ne : y ≠ (block195S2 : ℝ))
    (hy3ne : y ≠ (block195S3 : ℝ))
    (hy4ne : y ≠ (block195S4 : ℝ)) :
    0 < block195V y := by
  have hcert := block195RightChunk000Certificate_eq_true
  unfold block195RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block195RightChunk000) (lo := block195RightChunk000L) (hi := block195RightChunk000R)
    (w1 := block195W1) (w2 := block195W2) (w3 := block195W3) (w4 := block195W4)
    (s1 := block195S1) (s2 := block195S2) (s3 := block195S3) (s4 := block195S4)
    hboxes hcover block195RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block195RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block195RightChunk001 block195W1 block195W2 block195W3 block195W4 block195S1 block195S2 block195S3 block195S4

theorem block195RightChunk001ParamsCertificate_eq_true :
    block195RightChunk001ParamsCertificate = true := by
  native_decide

theorem block195_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block195RightChunk001L : ℝ) (block195RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block195S1 : ℝ))
    (hy2ne : y ≠ (block195S2 : ℝ))
    (hy3ne : y ≠ (block195S3 : ℝ))
    (hy4ne : y ≠ (block195S4 : ℝ)) :
    0 < block195V y := by
  have hcert := block195RightChunk001Certificate_eq_true
  unfold block195RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block195RightChunk001) (lo := block195RightChunk001L) (hi := block195RightChunk001R)
    (w1 := block195W1) (w2 := block195W2) (w3 := block195W3) (w4 := block195W4)
    (s1 := block195S1) (s2 := block195S2) (s3 := block195S3) (s4 := block195S4)
    hboxes hcover block195RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block195RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block195RightChunk002 block195W1 block195W2 block195W3 block195W4 block195S1 block195S2 block195S3 block195S4

theorem block195RightChunk002ParamsCertificate_eq_true :
    block195RightChunk002ParamsCertificate = true := by
  native_decide

theorem block195_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block195RightChunk002L : ℝ) (block195RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block195S1 : ℝ))
    (hy2ne : y ≠ (block195S2 : ℝ))
    (hy3ne : y ≠ (block195S3 : ℝ))
    (hy4ne : y ≠ (block195S4 : ℝ)) :
    0 < block195V y := by
  have hcert := block195RightChunk002Certificate_eq_true
  unfold block195RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block195RightChunk002) (lo := block195RightChunk002L) (hi := block195RightChunk002R)
    (w1 := block195W1) (w2 := block195W2) (w3 := block195W3) (w4 := block195W4)
    (s1 := block195S1) (s2 := block195S2) (s3 := block195S3) (s4 := block195S4)
    hboxes hcover block195RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block195RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block195RightChunk003 block195W1 block195W2 block195W3 block195W4 block195S1 block195S2 block195S3 block195S4

theorem block195RightChunk003ParamsCertificate_eq_true :
    block195RightChunk003ParamsCertificate = true := by
  native_decide

theorem block195_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block195RightChunk003L : ℝ) (block195RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block195S1 : ℝ))
    (hy2ne : y ≠ (block195S2 : ℝ))
    (hy3ne : y ≠ (block195S3 : ℝ))
    (hy4ne : y ≠ (block195S4 : ℝ)) :
    0 < block195V y := by
  have hcert := block195RightChunk003Certificate_eq_true
  unfold block195RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block195RightChunk003) (lo := block195RightChunk003L) (hi := block195RightChunk003R)
    (w1 := block195W1) (w2 := block195W2) (w3 := block195W3) (w4 := block195W4)
    (s1 := block195S1) (s2 := block195S2) (s3 := block195S3) (s4 := block195S4)
    hboxes hcover block195RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block195RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block195RightChunk004 block195W1 block195W2 block195W3 block195W4 block195S1 block195S2 block195S3 block195S4

theorem block195RightChunk004ParamsCertificate_eq_true :
    block195RightChunk004ParamsCertificate = true := by
  native_decide

theorem block195_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block195RightChunk004L : ℝ) (block195RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block195S1 : ℝ))
    (hy2ne : y ≠ (block195S2 : ℝ))
    (hy3ne : y ≠ (block195S3 : ℝ))
    (hy4ne : y ≠ (block195S4 : ℝ)) :
    0 < block195V y := by
  have hcert := block195RightChunk004Certificate_eq_true
  unfold block195RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block195RightChunk004) (lo := block195RightChunk004L) (hi := block195RightChunk004R)
    (w1 := block195W1) (w2 := block195W2) (w3 := block195W3) (w4 := block195W4)
    (s1 := block195S1) (s2 := block195S2) (s3 := block195S3) (s4 := block195S4)
    hboxes hcover block195RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block195RightChunk005ParamsCertificate : Bool :=
  allBoxesSameParams block195RightChunk005 block195W1 block195W2 block195W3 block195W4 block195S1 block195S2 block195S3 block195S4

theorem block195RightChunk005ParamsCertificate_eq_true :
    block195RightChunk005ParamsCertificate = true := by
  native_decide

theorem block195_right_chunk005_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block195RightChunk005L : ℝ) (block195RightChunk005R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block195S1 : ℝ))
    (hy2ne : y ≠ (block195S2 : ℝ))
    (hy3ne : y ≠ (block195S3 : ℝ))
    (hy4ne : y ≠ (block195S4 : ℝ)) :
    0 < block195V y := by
  have hcert := block195RightChunk005Certificate_eq_true
  unfold block195RightChunk005Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block195RightChunk005) (lo := block195RightChunk005L) (hi := block195RightChunk005R)
    (w1 := block195W1) (w2 := block195W2) (w3 := block195W3) (w4 := block195W4)
    (s1 := block195S1) (s2 := block195S2) (s3 := block195S3) (s4 := block195S4)
    hboxes hcover block195RightChunk005ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block195RightChunk006ParamsCertificate : Bool :=
  allBoxesSameParams block195RightChunk006 block195W1 block195W2 block195W3 block195W4 block195S1 block195S2 block195S3 block195S4

theorem block195RightChunk006ParamsCertificate_eq_true :
    block195RightChunk006ParamsCertificate = true := by
  native_decide

theorem block195_right_chunk006_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block195RightChunk006L : ℝ) (block195RightChunk006R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block195S1 : ℝ))
    (hy2ne : y ≠ (block195S2 : ℝ))
    (hy3ne : y ≠ (block195S3 : ℝ))
    (hy4ne : y ≠ (block195S4 : ℝ)) :
    0 < block195V y := by
  have hcert := block195RightChunk006Certificate_eq_true
  unfold block195RightChunk006Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block195RightChunk006) (lo := block195RightChunk006L) (hi := block195RightChunk006R)
    (w1 := block195W1) (w2 := block195W2) (w3 := block195W3) (w4 := block195W4)
    (s1 := block195S1) (s2 := block195S2) (s3 := block195S3) (s4 := block195S4)
    hboxes hcover block195RightChunk006ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block195RightChunk007ParamsCertificate : Bool :=
  allBoxesSameParams block195RightChunk007 block195W1 block195W2 block195W3 block195W4 block195S1 block195S2 block195S3 block195S4

theorem block195RightChunk007ParamsCertificate_eq_true :
    block195RightChunk007ParamsCertificate = true := by
  native_decide

theorem block195_right_chunk007_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block195RightChunk007L : ℝ) (block195RightChunk007R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block195S1 : ℝ))
    (hy2ne : y ≠ (block195S2 : ℝ))
    (hy3ne : y ≠ (block195S3 : ℝ))
    (hy4ne : y ≠ (block195S4 : ℝ)) :
    0 < block195V y := by
  have hcert := block195RightChunk007Certificate_eq_true
  unfold block195RightChunk007Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block195RightChunk007) (lo := block195RightChunk007L) (hi := block195RightChunk007R)
    (w1 := block195W1) (w2 := block195W2) (w3 := block195W3) (w4 := block195W4)
    (s1 := block195S1) (s2 := block195S2) (s3 := block195S3) (s4 := block195S4)
    hboxes hcover block195RightChunk007ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block195_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block195RightL : ℝ) (block195RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block195S1 : ℝ))
    (hy2ne : y ≠ (block195S2 : ℝ))
    (hy3ne : y ≠ (block195S3 : ℝ))
    (hy4ne : y ≠ (block195S4 : ℝ)) :
    0 < block195V y := by
  by_cases h0 : y ≤ (block195RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block195RightChunk000L : ℝ) (block195RightChunk000R : ℝ) := by
      have hL : (block195RightChunk000L : ℝ) = (block195RightL : ℝ) := by
        norm_num [block195RightChunk000L, block195RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block195_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block195RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block195RightChunk001L : ℝ) (block195RightChunk001R : ℝ) := by
        have hprev : (block195RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block195RightChunk001L : ℝ) = (block195RightChunk000R : ℝ) := by
          norm_num [block195RightChunk001L, block195RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block195_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block195RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block195RightChunk002L : ℝ) (block195RightChunk002R : ℝ) := by
          have hprev : (block195RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block195RightChunk002L : ℝ) = (block195RightChunk001R : ℝ) := by
            norm_num [block195RightChunk002L, block195RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block195_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block195RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block195RightChunk003L : ℝ) (block195RightChunk003R : ℝ) := by
            have hprev : (block195RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block195RightChunk003L : ℝ) = (block195RightChunk002R : ℝ) := by
              norm_num [block195RightChunk003L, block195RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block195_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          by_cases h4 : y ≤ (block195RightChunk004R : ℝ)
          · have hyc : y ∈ Icc (block195RightChunk004L : ℝ) (block195RightChunk004R : ℝ) := by
              have hprev : (block195RightChunk003R : ℝ) < y := lt_of_not_ge h3
              have hL : (block195RightChunk004L : ℝ) = (block195RightChunk003R : ℝ) := by
                norm_num [block195RightChunk004L, block195RightChunk003R]
              constructor
              · linarith [hprev, hL]
              · exact h4
            exact block195_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
          ·
            by_cases h5 : y ≤ (block195RightChunk005R : ℝ)
            · have hyc : y ∈ Icc (block195RightChunk005L : ℝ) (block195RightChunk005R : ℝ) := by
                have hprev : (block195RightChunk004R : ℝ) < y := lt_of_not_ge h4
                have hL : (block195RightChunk005L : ℝ) = (block195RightChunk004R : ℝ) := by
                  norm_num [block195RightChunk005L, block195RightChunk004R]
                constructor
                · linarith [hprev, hL]
                · exact h5
              exact block195_right_chunk005_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
            ·
              by_cases h6 : y ≤ (block195RightChunk006R : ℝ)
              · have hyc : y ∈ Icc (block195RightChunk006L : ℝ) (block195RightChunk006R : ℝ) := by
                  have hprev : (block195RightChunk005R : ℝ) < y := lt_of_not_ge h5
                  have hL : (block195RightChunk006L : ℝ) = (block195RightChunk005R : ℝ) := by
                    norm_num [block195RightChunk006L, block195RightChunk005R]
                  constructor
                  · linarith [hprev, hL]
                  · exact h6
                exact block195_right_chunk006_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
              ·
                have hprev : (block195RightChunk006R : ℝ) < y := lt_of_not_ge h6
                have hL : (block195RightChunk007L : ℝ) = (block195RightChunk006R : ℝ) := by
                  norm_num [block195RightChunk007L, block195RightChunk006R]
                have hR : (block195RightChunk007R : ℝ) = (block195RightR : ℝ) := by
                  norm_num [block195RightChunk007R, block195RightR]
                have hyc : y ∈ Icc (block195RightChunk007L : ℝ) (block195RightChunk007R : ℝ) := by
                  constructor
                  · linarith [hprev, hL]
                  · linarith [hy.2, hR]
                exact block195_right_chunk007_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block195_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block195LeftL : ℝ) (block195LeftR : ℝ) →
    y ≠ 0 → y ≠ (block195S1 : ℝ) → y ≠ (block195S2 : ℝ) →
    y ≠ (block195S3 : ℝ) → y ≠ (block195S4 : ℝ) → 0 < block195V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block195RightL : ℝ) (block195RightR : ℝ) →
    y ≠ 0 → y ≠ (block195S1 : ℝ) → y ≠ (block195S2 : ℝ) →
    y ≠ (block195S3 : ℝ) → y ≠ (block195S4 : ℝ) → 0 < block195V y)

theorem block195_reallog_certificate_proof :
    block195_reallog_certificate := by
  exact ⟨block195_left_V_pos, block195_right_V_pos⟩

end Block195
end M1817475
end Erdos1038Lean
