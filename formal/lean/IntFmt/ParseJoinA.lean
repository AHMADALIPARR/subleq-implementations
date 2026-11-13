/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Compose named parse/image chunk lemmas for lines 0–49 via
`parseDecText_append` and `extract_split`. Group results are
combined through named prefix definitions so Lean does not
reduce a long concatenation in a theorem type.
-/

import IntFmt.ParseJoinCore
import IntFmt.DecBindDataA

namespace IntFmt

set_option maxHeartbeats 800000
set_option maxRecDepth 20000

@[irreducible] def text_000_004 : String := decLine000 ++ decLine001 ++ decLine002 ++ decLine003 ++ decLine004
@[irreducible] def image_000_004 : Array UInt16 := ((((decChunk000 ++ decChunk001) ++ decChunk002) ++ decChunk003) ++ decChunk004)
private theorem ws_000_004_0 : listEndsWS decLine000.toList :=
  decLine000_ws
private theorem ws_000_004_1 : listEndsWS (decLine000 ++ decLine001).toList :=
  ws_cat (decLine000) decLine001 ws_000_004_0 decLine001_ws
private theorem ws_000_004_2 : listEndsWS (decLine000 ++ decLine001 ++ decLine002).toList :=
  ws_cat (decLine000 ++ decLine001) decLine002 ws_000_004_1 decLine002_ws
private theorem ws_000_004_3 : listEndsWS (decLine000 ++ decLine001 ++ decLine002 ++ decLine003).toList :=
  ws_cat (decLine000 ++ decLine001 ++ decLine002) decLine003 ws_000_004_2 decLine003_ws
private theorem ws_000_004_4 : listEndsWS (decLine000 ++ decLine001 ++ decLine002 ++ decLine003 ++ decLine004).toList :=
  ws_cat (decLine000 ++ decLine001 ++ decLine002 ++ decLine003) decLine004 ws_000_004_3 decLine004_ws
theorem parse_000_004 : parseDecText text_000_004 = image_000_004 := by
  have p1 := parse_append_eq decLine000 decLine001
    decChunk000 decChunk001
    ws_000_004_0 parse_line000 parse_line001
  have p2 := parse_append_eq (decLine000 ++ decLine001) decLine002
    (decChunk000 ++ decChunk001) decChunk002
    ws_000_004_1 p1 parse_line002
  have p3 := parse_append_eq (decLine000 ++ decLine001 ++ decLine002) decLine003
    ((decChunk000 ++ decChunk001) ++ decChunk002) decChunk003
    ws_000_004_2 p2 parse_line003
  have p4 := parse_append_eq (decLine000 ++ decLine001 ++ decLine002 ++ decLine003) decLine004
    (((decChunk000 ++ decChunk001) ++ decChunk002) ++ decChunk003) decChunk004
    ws_000_004_3 p3 parse_line004
  rw [text_000_004, image_000_004]
  exact p4
theorem extract_000_004 :
    intfmtImage.extract 0 80 = image_000_004 := by
  have i1 := extract_append_eq 0 16 32
    decChunk000 decChunk001
    (by decide) (by decide) (by decide)
    image_chunk000 image_chunk001
  have i2 := extract_append_eq 0 32 48
    (decChunk000 ++ decChunk001) decChunk002
    (by decide) (by decide) (by decide)
    i1 image_chunk002
  have i3 := extract_append_eq 0 48 64
    ((decChunk000 ++ decChunk001) ++ decChunk002) decChunk003
    (by decide) (by decide) (by decide)
    i2 image_chunk003
  have i4 := extract_append_eq 0 64 80
    (((decChunk000 ++ decChunk001) ++ decChunk002) ++ decChunk003) decChunk004
    (by decide) (by decide) (by decide)
    i3 image_chunk004
  rw [image_000_004]
  exact i4
private theorem ws_text_000_004 : listEndsWS text_000_004.toList := by
  unfold text_000_004
  exact ws_000_004_4

@[irreducible] def text_005_009 : String := decLine005 ++ decLine006 ++ decLine007 ++ decLine008 ++ decLine009
@[irreducible] def image_005_009 : Array UInt16 := ((((decChunk005 ++ decChunk006) ++ decChunk007) ++ decChunk008) ++ decChunk009)
private theorem ws_005_009_0 : listEndsWS decLine005.toList :=
  decLine005_ws
private theorem ws_005_009_1 : listEndsWS (decLine005 ++ decLine006).toList :=
  ws_cat (decLine005) decLine006 ws_005_009_0 decLine006_ws
private theorem ws_005_009_2 : listEndsWS (decLine005 ++ decLine006 ++ decLine007).toList :=
  ws_cat (decLine005 ++ decLine006) decLine007 ws_005_009_1 decLine007_ws
private theorem ws_005_009_3 : listEndsWS (decLine005 ++ decLine006 ++ decLine007 ++ decLine008).toList :=
  ws_cat (decLine005 ++ decLine006 ++ decLine007) decLine008 ws_005_009_2 decLine008_ws
private theorem ws_005_009_4 : listEndsWS (decLine005 ++ decLine006 ++ decLine007 ++ decLine008 ++ decLine009).toList :=
  ws_cat (decLine005 ++ decLine006 ++ decLine007 ++ decLine008) decLine009 ws_005_009_3 decLine009_ws
theorem parse_005_009 : parseDecText text_005_009 = image_005_009 := by
  have p1 := parse_append_eq decLine005 decLine006
    decChunk005 decChunk006
    ws_005_009_0 parse_line005 parse_line006
  have p2 := parse_append_eq (decLine005 ++ decLine006) decLine007
    (decChunk005 ++ decChunk006) decChunk007
    ws_005_009_1 p1 parse_line007
  have p3 := parse_append_eq (decLine005 ++ decLine006 ++ decLine007) decLine008
    ((decChunk005 ++ decChunk006) ++ decChunk007) decChunk008
    ws_005_009_2 p2 parse_line008
  have p4 := parse_append_eq (decLine005 ++ decLine006 ++ decLine007 ++ decLine008) decLine009
    (((decChunk005 ++ decChunk006) ++ decChunk007) ++ decChunk008) decChunk009
    ws_005_009_3 p3 parse_line009
  rw [text_005_009, image_005_009]
  exact p4
theorem extract_005_009 :
    intfmtImage.extract 80 160 = image_005_009 := by
  have i1 := extract_append_eq 80 96 112
    decChunk005 decChunk006
    (by decide) (by decide) (by decide)
    image_chunk005 image_chunk006
  have i2 := extract_append_eq 80 112 128
    (decChunk005 ++ decChunk006) decChunk007
    (by decide) (by decide) (by decide)
    i1 image_chunk007
  have i3 := extract_append_eq 80 128 144
    ((decChunk005 ++ decChunk006) ++ decChunk007) decChunk008
    (by decide) (by decide) (by decide)
    i2 image_chunk008
  have i4 := extract_append_eq 80 144 160
    (((decChunk005 ++ decChunk006) ++ decChunk007) ++ decChunk008) decChunk009
    (by decide) (by decide) (by decide)
    i3 image_chunk009
  rw [image_005_009]
  exact i4
private theorem ws_text_005_009 : listEndsWS text_005_009.toList := by
  unfold text_005_009
  exact ws_005_009_4

@[irreducible] def text_010_014 : String := decLine010 ++ decLine011 ++ decLine012 ++ decLine013 ++ decLine014
@[irreducible] def image_010_014 : Array UInt16 := ((((decChunk010 ++ decChunk011) ++ decChunk012) ++ decChunk013) ++ decChunk014)
private theorem ws_010_014_0 : listEndsWS decLine010.toList :=
  decLine010_ws
private theorem ws_010_014_1 : listEndsWS (decLine010 ++ decLine011).toList :=
  ws_cat (decLine010) decLine011 ws_010_014_0 decLine011_ws
private theorem ws_010_014_2 : listEndsWS (decLine010 ++ decLine011 ++ decLine012).toList :=
  ws_cat (decLine010 ++ decLine011) decLine012 ws_010_014_1 decLine012_ws
private theorem ws_010_014_3 : listEndsWS (decLine010 ++ decLine011 ++ decLine012 ++ decLine013).toList :=
  ws_cat (decLine010 ++ decLine011 ++ decLine012) decLine013 ws_010_014_2 decLine013_ws
private theorem ws_010_014_4 : listEndsWS (decLine010 ++ decLine011 ++ decLine012 ++ decLine013 ++ decLine014).toList :=
  ws_cat (decLine010 ++ decLine011 ++ decLine012 ++ decLine013) decLine014 ws_010_014_3 decLine014_ws
theorem parse_010_014 : parseDecText text_010_014 = image_010_014 := by
  have p1 := parse_append_eq decLine010 decLine011
    decChunk010 decChunk011
    ws_010_014_0 parse_line010 parse_line011
  have p2 := parse_append_eq (decLine010 ++ decLine011) decLine012
    (decChunk010 ++ decChunk011) decChunk012
    ws_010_014_1 p1 parse_line012
  have p3 := parse_append_eq (decLine010 ++ decLine011 ++ decLine012) decLine013
    ((decChunk010 ++ decChunk011) ++ decChunk012) decChunk013
    ws_010_014_2 p2 parse_line013
  have p4 := parse_append_eq (decLine010 ++ decLine011 ++ decLine012 ++ decLine013) decLine014
    (((decChunk010 ++ decChunk011) ++ decChunk012) ++ decChunk013) decChunk014
    ws_010_014_3 p3 parse_line014
  rw [text_010_014, image_010_014]
  exact p4
theorem extract_010_014 :
    intfmtImage.extract 160 240 = image_010_014 := by
  have i1 := extract_append_eq 160 176 192
    decChunk010 decChunk011
    (by decide) (by decide) (by decide)
    image_chunk010 image_chunk011
  have i2 := extract_append_eq 160 192 208
    (decChunk010 ++ decChunk011) decChunk012
    (by decide) (by decide) (by decide)
    i1 image_chunk012
  have i3 := extract_append_eq 160 208 224
    ((decChunk010 ++ decChunk011) ++ decChunk012) decChunk013
    (by decide) (by decide) (by decide)
    i2 image_chunk013
  have i4 := extract_append_eq 160 224 240
    (((decChunk010 ++ decChunk011) ++ decChunk012) ++ decChunk013) decChunk014
    (by decide) (by decide) (by decide)
    i3 image_chunk014
  rw [image_010_014]
  exact i4
private theorem ws_text_010_014 : listEndsWS text_010_014.toList := by
  unfold text_010_014
  exact ws_010_014_4

@[irreducible] def text_015_019 : String := decLine015 ++ decLine016 ++ decLine017 ++ decLine018 ++ decLine019
@[irreducible] def image_015_019 : Array UInt16 := ((((decChunk015 ++ decChunk016) ++ decChunk017) ++ decChunk018) ++ decChunk019)
private theorem ws_015_019_0 : listEndsWS decLine015.toList :=
  decLine015_ws
private theorem ws_015_019_1 : listEndsWS (decLine015 ++ decLine016).toList :=
  ws_cat (decLine015) decLine016 ws_015_019_0 decLine016_ws
private theorem ws_015_019_2 : listEndsWS (decLine015 ++ decLine016 ++ decLine017).toList :=
  ws_cat (decLine015 ++ decLine016) decLine017 ws_015_019_1 decLine017_ws
private theorem ws_015_019_3 : listEndsWS (decLine015 ++ decLine016 ++ decLine017 ++ decLine018).toList :=
  ws_cat (decLine015 ++ decLine016 ++ decLine017) decLine018 ws_015_019_2 decLine018_ws
private theorem ws_015_019_4 : listEndsWS (decLine015 ++ decLine016 ++ decLine017 ++ decLine018 ++ decLine019).toList :=
  ws_cat (decLine015 ++ decLine016 ++ decLine017 ++ decLine018) decLine019 ws_015_019_3 decLine019_ws
theorem parse_015_019 : parseDecText text_015_019 = image_015_019 := by
  have p1 := parse_append_eq decLine015 decLine016
    decChunk015 decChunk016
    ws_015_019_0 parse_line015 parse_line016
  have p2 := parse_append_eq (decLine015 ++ decLine016) decLine017
    (decChunk015 ++ decChunk016) decChunk017
    ws_015_019_1 p1 parse_line017
  have p3 := parse_append_eq (decLine015 ++ decLine016 ++ decLine017) decLine018
    ((decChunk015 ++ decChunk016) ++ decChunk017) decChunk018
    ws_015_019_2 p2 parse_line018
  have p4 := parse_append_eq (decLine015 ++ decLine016 ++ decLine017 ++ decLine018) decLine019
    (((decChunk015 ++ decChunk016) ++ decChunk017) ++ decChunk018) decChunk019
    ws_015_019_3 p3 parse_line019
  rw [text_015_019, image_015_019]
  exact p4
theorem extract_015_019 :
    intfmtImage.extract 240 320 = image_015_019 := by
  have i1 := extract_append_eq 240 256 272
    decChunk015 decChunk016
    (by decide) (by decide) (by decide)
    image_chunk015 image_chunk016
  have i2 := extract_append_eq 240 272 288
    (decChunk015 ++ decChunk016) decChunk017
    (by decide) (by decide) (by decide)
    i1 image_chunk017
  have i3 := extract_append_eq 240 288 304
    ((decChunk015 ++ decChunk016) ++ decChunk017) decChunk018
    (by decide) (by decide) (by decide)
    i2 image_chunk018
  have i4 := extract_append_eq 240 304 320
    (((decChunk015 ++ decChunk016) ++ decChunk017) ++ decChunk018) decChunk019
    (by decide) (by decide) (by decide)
    i3 image_chunk019
  rw [image_015_019]
  exact i4
private theorem ws_text_015_019 : listEndsWS text_015_019.toList := by
  unfold text_015_019
  exact ws_015_019_4

@[irreducible] def text_020_024 : String := decLine020 ++ decLine021 ++ decLine022 ++ decLine023 ++ decLine024
@[irreducible] def image_020_024 : Array UInt16 := ((((decChunk020 ++ decChunk021) ++ decChunk022) ++ decChunk023) ++ decChunk024)
private theorem ws_020_024_0 : listEndsWS decLine020.toList :=
  decLine020_ws
private theorem ws_020_024_1 : listEndsWS (decLine020 ++ decLine021).toList :=
  ws_cat (decLine020) decLine021 ws_020_024_0 decLine021_ws
private theorem ws_020_024_2 : listEndsWS (decLine020 ++ decLine021 ++ decLine022).toList :=
  ws_cat (decLine020 ++ decLine021) decLine022 ws_020_024_1 decLine022_ws
private theorem ws_020_024_3 : listEndsWS (decLine020 ++ decLine021 ++ decLine022 ++ decLine023).toList :=
  ws_cat (decLine020 ++ decLine021 ++ decLine022) decLine023 ws_020_024_2 decLine023_ws
private theorem ws_020_024_4 : listEndsWS (decLine020 ++ decLine021 ++ decLine022 ++ decLine023 ++ decLine024).toList :=
  ws_cat (decLine020 ++ decLine021 ++ decLine022 ++ decLine023) decLine024 ws_020_024_3 decLine024_ws
theorem parse_020_024 : parseDecText text_020_024 = image_020_024 := by
  have p1 := parse_append_eq decLine020 decLine021
    decChunk020 decChunk021
    ws_020_024_0 parse_line020 parse_line021
  have p2 := parse_append_eq (decLine020 ++ decLine021) decLine022
    (decChunk020 ++ decChunk021) decChunk022
    ws_020_024_1 p1 parse_line022
  have p3 := parse_append_eq (decLine020 ++ decLine021 ++ decLine022) decLine023
    ((decChunk020 ++ decChunk021) ++ decChunk022) decChunk023
    ws_020_024_2 p2 parse_line023
  have p4 := parse_append_eq (decLine020 ++ decLine021 ++ decLine022 ++ decLine023) decLine024
    (((decChunk020 ++ decChunk021) ++ decChunk022) ++ decChunk023) decChunk024
    ws_020_024_3 p3 parse_line024
  rw [text_020_024, image_020_024]
  exact p4
theorem extract_020_024 :
    intfmtImage.extract 320 400 = image_020_024 := by
  have i1 := extract_append_eq 320 336 352
    decChunk020 decChunk021
    (by decide) (by decide) (by decide)
    image_chunk020 image_chunk021
  have i2 := extract_append_eq 320 352 368
    (decChunk020 ++ decChunk021) decChunk022
    (by decide) (by decide) (by decide)
    i1 image_chunk022
  have i3 := extract_append_eq 320 368 384
    ((decChunk020 ++ decChunk021) ++ decChunk022) decChunk023
    (by decide) (by decide) (by decide)
    i2 image_chunk023
  have i4 := extract_append_eq 320 384 400
    (((decChunk020 ++ decChunk021) ++ decChunk022) ++ decChunk023) decChunk024
    (by decide) (by decide) (by decide)
    i3 image_chunk024
  rw [image_020_024]
  exact i4
private theorem ws_text_020_024 : listEndsWS text_020_024.toList := by
  unfold text_020_024
  exact ws_020_024_4

@[irreducible] def text_025_029 : String := decLine025 ++ decLine026 ++ decLine027 ++ decLine028 ++ decLine029
@[irreducible] def image_025_029 : Array UInt16 := ((((decChunk025 ++ decChunk026) ++ decChunk027) ++ decChunk028) ++ decChunk029)
private theorem ws_025_029_0 : listEndsWS decLine025.toList :=
  decLine025_ws
private theorem ws_025_029_1 : listEndsWS (decLine025 ++ decLine026).toList :=
  ws_cat (decLine025) decLine026 ws_025_029_0 decLine026_ws
private theorem ws_025_029_2 : listEndsWS (decLine025 ++ decLine026 ++ decLine027).toList :=
  ws_cat (decLine025 ++ decLine026) decLine027 ws_025_029_1 decLine027_ws
private theorem ws_025_029_3 : listEndsWS (decLine025 ++ decLine026 ++ decLine027 ++ decLine028).toList :=
  ws_cat (decLine025 ++ decLine026 ++ decLine027) decLine028 ws_025_029_2 decLine028_ws
private theorem ws_025_029_4 : listEndsWS (decLine025 ++ decLine026 ++ decLine027 ++ decLine028 ++ decLine029).toList :=
  ws_cat (decLine025 ++ decLine026 ++ decLine027 ++ decLine028) decLine029 ws_025_029_3 decLine029_ws
theorem parse_025_029 : parseDecText text_025_029 = image_025_029 := by
  have p1 := parse_append_eq decLine025 decLine026
    decChunk025 decChunk026
    ws_025_029_0 parse_line025 parse_line026
  have p2 := parse_append_eq (decLine025 ++ decLine026) decLine027
    (decChunk025 ++ decChunk026) decChunk027
    ws_025_029_1 p1 parse_line027
  have p3 := parse_append_eq (decLine025 ++ decLine026 ++ decLine027) decLine028
    ((decChunk025 ++ decChunk026) ++ decChunk027) decChunk028
    ws_025_029_2 p2 parse_line028
  have p4 := parse_append_eq (decLine025 ++ decLine026 ++ decLine027 ++ decLine028) decLine029
    (((decChunk025 ++ decChunk026) ++ decChunk027) ++ decChunk028) decChunk029
    ws_025_029_3 p3 parse_line029
  rw [text_025_029, image_025_029]
  exact p4
theorem extract_025_029 :
    intfmtImage.extract 400 480 = image_025_029 := by
  have i1 := extract_append_eq 400 416 432
    decChunk025 decChunk026
    (by decide) (by decide) (by decide)
    image_chunk025 image_chunk026
  have i2 := extract_append_eq 400 432 448
    (decChunk025 ++ decChunk026) decChunk027
    (by decide) (by decide) (by decide)
    i1 image_chunk027
  have i3 := extract_append_eq 400 448 464
    ((decChunk025 ++ decChunk026) ++ decChunk027) decChunk028
    (by decide) (by decide) (by decide)
    i2 image_chunk028
  have i4 := extract_append_eq 400 464 480
    (((decChunk025 ++ decChunk026) ++ decChunk027) ++ decChunk028) decChunk029
    (by decide) (by decide) (by decide)
    i3 image_chunk029
  rw [image_025_029]
  exact i4
private theorem ws_text_025_029 : listEndsWS text_025_029.toList := by
  unfold text_025_029
  exact ws_025_029_4

@[irreducible] def text_030_034 : String := decLine030 ++ decLine031 ++ decLine032 ++ decLine033 ++ decLine034
@[irreducible] def image_030_034 : Array UInt16 := ((((decChunk030 ++ decChunk031) ++ decChunk032) ++ decChunk033) ++ decChunk034)
private theorem ws_030_034_0 : listEndsWS decLine030.toList :=
  decLine030_ws
private theorem ws_030_034_1 : listEndsWS (decLine030 ++ decLine031).toList :=
  ws_cat (decLine030) decLine031 ws_030_034_0 decLine031_ws
private theorem ws_030_034_2 : listEndsWS (decLine030 ++ decLine031 ++ decLine032).toList :=
  ws_cat (decLine030 ++ decLine031) decLine032 ws_030_034_1 decLine032_ws
private theorem ws_030_034_3 : listEndsWS (decLine030 ++ decLine031 ++ decLine032 ++ decLine033).toList :=
  ws_cat (decLine030 ++ decLine031 ++ decLine032) decLine033 ws_030_034_2 decLine033_ws
private theorem ws_030_034_4 : listEndsWS (decLine030 ++ decLine031 ++ decLine032 ++ decLine033 ++ decLine034).toList :=
  ws_cat (decLine030 ++ decLine031 ++ decLine032 ++ decLine033) decLine034 ws_030_034_3 decLine034_ws
theorem parse_030_034 : parseDecText text_030_034 = image_030_034 := by
  have p1 := parse_append_eq decLine030 decLine031
    decChunk030 decChunk031
    ws_030_034_0 parse_line030 parse_line031
  have p2 := parse_append_eq (decLine030 ++ decLine031) decLine032
    (decChunk030 ++ decChunk031) decChunk032
    ws_030_034_1 p1 parse_line032
  have p3 := parse_append_eq (decLine030 ++ decLine031 ++ decLine032) decLine033
    ((decChunk030 ++ decChunk031) ++ decChunk032) decChunk033
    ws_030_034_2 p2 parse_line033
  have p4 := parse_append_eq (decLine030 ++ decLine031 ++ decLine032 ++ decLine033) decLine034
    (((decChunk030 ++ decChunk031) ++ decChunk032) ++ decChunk033) decChunk034
    ws_030_034_3 p3 parse_line034
  rw [text_030_034, image_030_034]
  exact p4
theorem extract_030_034 :
    intfmtImage.extract 480 560 = image_030_034 := by
  have i1 := extract_append_eq 480 496 512
    decChunk030 decChunk031
    (by decide) (by decide) (by decide)
    image_chunk030 image_chunk031
  have i2 := extract_append_eq 480 512 528
    (decChunk030 ++ decChunk031) decChunk032
    (by decide) (by decide) (by decide)
    i1 image_chunk032
  have i3 := extract_append_eq 480 528 544
    ((decChunk030 ++ decChunk031) ++ decChunk032) decChunk033
    (by decide) (by decide) (by decide)
    i2 image_chunk033
  have i4 := extract_append_eq 480 544 560
    (((decChunk030 ++ decChunk031) ++ decChunk032) ++ decChunk033) decChunk034
    (by decide) (by decide) (by decide)
    i3 image_chunk034
  rw [image_030_034]
  exact i4
private theorem ws_text_030_034 : listEndsWS text_030_034.toList := by
  unfold text_030_034
  exact ws_030_034_4

@[irreducible] def text_035_039 : String := decLine035 ++ decLine036 ++ decLine037 ++ decLine038 ++ decLine039
@[irreducible] def image_035_039 : Array UInt16 := ((((decChunk035 ++ decChunk036) ++ decChunk037) ++ decChunk038) ++ decChunk039)
private theorem ws_035_039_0 : listEndsWS decLine035.toList :=
  decLine035_ws
private theorem ws_035_039_1 : listEndsWS (decLine035 ++ decLine036).toList :=
  ws_cat (decLine035) decLine036 ws_035_039_0 decLine036_ws
private theorem ws_035_039_2 : listEndsWS (decLine035 ++ decLine036 ++ decLine037).toList :=
  ws_cat (decLine035 ++ decLine036) decLine037 ws_035_039_1 decLine037_ws
private theorem ws_035_039_3 : listEndsWS (decLine035 ++ decLine036 ++ decLine037 ++ decLine038).toList :=
  ws_cat (decLine035 ++ decLine036 ++ decLine037) decLine038 ws_035_039_2 decLine038_ws
private theorem ws_035_039_4 : listEndsWS (decLine035 ++ decLine036 ++ decLine037 ++ decLine038 ++ decLine039).toList :=
  ws_cat (decLine035 ++ decLine036 ++ decLine037 ++ decLine038) decLine039 ws_035_039_3 decLine039_ws
theorem parse_035_039 : parseDecText text_035_039 = image_035_039 := by
  have p1 := parse_append_eq decLine035 decLine036
    decChunk035 decChunk036
    ws_035_039_0 parse_line035 parse_line036
  have p2 := parse_append_eq (decLine035 ++ decLine036) decLine037
    (decChunk035 ++ decChunk036) decChunk037
    ws_035_039_1 p1 parse_line037
  have p3 := parse_append_eq (decLine035 ++ decLine036 ++ decLine037) decLine038
    ((decChunk035 ++ decChunk036) ++ decChunk037) decChunk038
    ws_035_039_2 p2 parse_line038
  have p4 := parse_append_eq (decLine035 ++ decLine036 ++ decLine037 ++ decLine038) decLine039
    (((decChunk035 ++ decChunk036) ++ decChunk037) ++ decChunk038) decChunk039
    ws_035_039_3 p3 parse_line039
  rw [text_035_039, image_035_039]
  exact p4
theorem extract_035_039 :
    intfmtImage.extract 560 640 = image_035_039 := by
  have i1 := extract_append_eq 560 576 592
    decChunk035 decChunk036
    (by decide) (by decide) (by decide)
    image_chunk035 image_chunk036
  have i2 := extract_append_eq 560 592 608
    (decChunk035 ++ decChunk036) decChunk037
    (by decide) (by decide) (by decide)
    i1 image_chunk037
  have i3 := extract_append_eq 560 608 624
    ((decChunk035 ++ decChunk036) ++ decChunk037) decChunk038
    (by decide) (by decide) (by decide)
    i2 image_chunk038
  have i4 := extract_append_eq 560 624 640
    (((decChunk035 ++ decChunk036) ++ decChunk037) ++ decChunk038) decChunk039
    (by decide) (by decide) (by decide)
    i3 image_chunk039
  rw [image_035_039]
  exact i4
private theorem ws_text_035_039 : listEndsWS text_035_039.toList := by
  unfold text_035_039
  exact ws_035_039_4

@[irreducible] def text_040_044 : String := decLine040 ++ decLine041 ++ decLine042 ++ decLine043 ++ decLine044
@[irreducible] def image_040_044 : Array UInt16 := ((((decChunk040 ++ decChunk041) ++ decChunk042) ++ decChunk043) ++ decChunk044)
private theorem ws_040_044_0 : listEndsWS decLine040.toList :=
  decLine040_ws
private theorem ws_040_044_1 : listEndsWS (decLine040 ++ decLine041).toList :=
  ws_cat (decLine040) decLine041 ws_040_044_0 decLine041_ws
private theorem ws_040_044_2 : listEndsWS (decLine040 ++ decLine041 ++ decLine042).toList :=
  ws_cat (decLine040 ++ decLine041) decLine042 ws_040_044_1 decLine042_ws
private theorem ws_040_044_3 : listEndsWS (decLine040 ++ decLine041 ++ decLine042 ++ decLine043).toList :=
  ws_cat (decLine040 ++ decLine041 ++ decLine042) decLine043 ws_040_044_2 decLine043_ws
private theorem ws_040_044_4 : listEndsWS (decLine040 ++ decLine041 ++ decLine042 ++ decLine043 ++ decLine044).toList :=
  ws_cat (decLine040 ++ decLine041 ++ decLine042 ++ decLine043) decLine044 ws_040_044_3 decLine044_ws
theorem parse_040_044 : parseDecText text_040_044 = image_040_044 := by
  have p1 := parse_append_eq decLine040 decLine041
    decChunk040 decChunk041
    ws_040_044_0 parse_line040 parse_line041
  have p2 := parse_append_eq (decLine040 ++ decLine041) decLine042
    (decChunk040 ++ decChunk041) decChunk042
    ws_040_044_1 p1 parse_line042
  have p3 := parse_append_eq (decLine040 ++ decLine041 ++ decLine042) decLine043
    ((decChunk040 ++ decChunk041) ++ decChunk042) decChunk043
    ws_040_044_2 p2 parse_line043
  have p4 := parse_append_eq (decLine040 ++ decLine041 ++ decLine042 ++ decLine043) decLine044
    (((decChunk040 ++ decChunk041) ++ decChunk042) ++ decChunk043) decChunk044
    ws_040_044_3 p3 parse_line044
  rw [text_040_044, image_040_044]
  exact p4
theorem extract_040_044 :
    intfmtImage.extract 640 720 = image_040_044 := by
  have i1 := extract_append_eq 640 656 672
    decChunk040 decChunk041
    (by decide) (by decide) (by decide)
    image_chunk040 image_chunk041
  have i2 := extract_append_eq 640 672 688
    (decChunk040 ++ decChunk041) decChunk042
    (by decide) (by decide) (by decide)
    i1 image_chunk042
  have i3 := extract_append_eq 640 688 704
    ((decChunk040 ++ decChunk041) ++ decChunk042) decChunk043
    (by decide) (by decide) (by decide)
    i2 image_chunk043
  have i4 := extract_append_eq 640 704 720
    (((decChunk040 ++ decChunk041) ++ decChunk042) ++ decChunk043) decChunk044
    (by decide) (by decide) (by decide)
    i3 image_chunk044
  rw [image_040_044]
  exact i4
private theorem ws_text_040_044 : listEndsWS text_040_044.toList := by
  unfold text_040_044
  exact ws_040_044_4

@[irreducible] def text_045_049 : String := decLine045 ++ decLine046 ++ decLine047 ++ decLine048 ++ decLine049
@[irreducible] def image_045_049 : Array UInt16 := ((((decChunk045 ++ decChunk046) ++ decChunk047) ++ decChunk048) ++ decChunk049)
private theorem ws_045_049_0 : listEndsWS decLine045.toList :=
  decLine045_ws
private theorem ws_045_049_1 : listEndsWS (decLine045 ++ decLine046).toList :=
  ws_cat (decLine045) decLine046 ws_045_049_0 decLine046_ws
private theorem ws_045_049_2 : listEndsWS (decLine045 ++ decLine046 ++ decLine047).toList :=
  ws_cat (decLine045 ++ decLine046) decLine047 ws_045_049_1 decLine047_ws
private theorem ws_045_049_3 : listEndsWS (decLine045 ++ decLine046 ++ decLine047 ++ decLine048).toList :=
  ws_cat (decLine045 ++ decLine046 ++ decLine047) decLine048 ws_045_049_2 decLine048_ws
private theorem ws_045_049_4 : listEndsWS (decLine045 ++ decLine046 ++ decLine047 ++ decLine048 ++ decLine049).toList :=
  ws_cat (decLine045 ++ decLine046 ++ decLine047 ++ decLine048) decLine049 ws_045_049_3 decLine049_ws
theorem parse_045_049 : parseDecText text_045_049 = image_045_049 := by
  have p1 := parse_append_eq decLine045 decLine046
    decChunk045 decChunk046
    ws_045_049_0 parse_line045 parse_line046
  have p2 := parse_append_eq (decLine045 ++ decLine046) decLine047
    (decChunk045 ++ decChunk046) decChunk047
    ws_045_049_1 p1 parse_line047
  have p3 := parse_append_eq (decLine045 ++ decLine046 ++ decLine047) decLine048
    ((decChunk045 ++ decChunk046) ++ decChunk047) decChunk048
    ws_045_049_2 p2 parse_line048
  have p4 := parse_append_eq (decLine045 ++ decLine046 ++ decLine047 ++ decLine048) decLine049
    (((decChunk045 ++ decChunk046) ++ decChunk047) ++ decChunk048) decChunk049
    ws_045_049_3 p3 parse_line049
  rw [text_045_049, image_045_049]
  exact p4
theorem extract_045_049 :
    intfmtImage.extract 720 800 = image_045_049 := by
  have i1 := extract_append_eq 720 736 752
    decChunk045 decChunk046
    (by decide) (by decide) (by decide)
    image_chunk045 image_chunk046
  have i2 := extract_append_eq 720 752 768
    (decChunk045 ++ decChunk046) decChunk047
    (by decide) (by decide) (by decide)
    i1 image_chunk047
  have i3 := extract_append_eq 720 768 784
    ((decChunk045 ++ decChunk046) ++ decChunk047) decChunk048
    (by decide) (by decide) (by decide)
    i2 image_chunk048
  have i4 := extract_append_eq 720 784 800
    (((decChunk045 ++ decChunk046) ++ decChunk047) ++ decChunk048) decChunk049
    (by decide) (by decide) (by decide)
    i3 image_chunk049
  rw [image_045_049]
  exact i4
private theorem ws_text_045_049 : listEndsWS text_045_049.toList := by
  unfold text_045_049
  exact ws_045_049_4

@[irreducible] def joinA_pref1 : String := text_000_004 ++ text_005_009
@[irreducible] def joinA_img1 : Array UInt16 := image_000_004 ++ image_005_009
private theorem ws_joinA_pref1 : listEndsWS joinA_pref1.toList := by
  unfold joinA_pref1
  exact ws_cat text_000_004 text_005_009 ws_text_000_004 ws_text_005_009
theorem parse_joinA_pref1 :
    parseDecText joinA_pref1 = joinA_img1 := by
  have h := parse_append_eq text_000_004 text_005_009 image_000_004 image_005_009
    ws_text_000_004 parse_000_004 parse_005_009
  unfold joinA_pref1 joinA_img1
  exact h
theorem extract_joinA_pref1 :
    intfmtImage.extract 0 160 = joinA_img1 := by
  have h := extract_append_eq 0 80 160 image_000_004 image_005_009
    (by decide) (by decide) (by decide)
    extract_000_004 extract_005_009
  unfold joinA_img1
  exact h
@[irreducible] def joinA_pref2 : String := joinA_pref1 ++ text_010_014
@[irreducible] def joinA_img2 : Array UInt16 := joinA_img1 ++ image_010_014
private theorem ws_joinA_pref2 : listEndsWS joinA_pref2.toList := by
  unfold joinA_pref2
  exact ws_cat joinA_pref1 text_010_014 ws_joinA_pref1 ws_text_010_014
theorem parse_joinA_pref2 :
    parseDecText joinA_pref2 = joinA_img2 := by
  have h := parse_append_eq joinA_pref1 text_010_014
    joinA_img1 image_010_014
    ws_joinA_pref1 parse_joinA_pref1 parse_010_014
  unfold joinA_pref2 joinA_img2
  exact h
theorem extract_joinA_pref2 :
    intfmtImage.extract 0 240 = joinA_img2 := by
  have h := extract_append_eq 0 160 240
    joinA_img1 image_010_014
    (by decide) (by decide) (by decide)
    extract_joinA_pref1 extract_010_014
  unfold joinA_img2
  exact h
@[irreducible] def joinA_pref3 : String := joinA_pref2 ++ text_015_019
@[irreducible] def joinA_img3 : Array UInt16 := joinA_img2 ++ image_015_019
private theorem ws_joinA_pref3 : listEndsWS joinA_pref3.toList := by
  unfold joinA_pref3
  exact ws_cat joinA_pref2 text_015_019 ws_joinA_pref2 ws_text_015_019
theorem parse_joinA_pref3 :
    parseDecText joinA_pref3 = joinA_img3 := by
  have h := parse_append_eq joinA_pref2 text_015_019
    joinA_img2 image_015_019
    ws_joinA_pref2 parse_joinA_pref2 parse_015_019
  unfold joinA_pref3 joinA_img3
  exact h
theorem extract_joinA_pref3 :
    intfmtImage.extract 0 320 = joinA_img3 := by
  have h := extract_append_eq 0 240 320
    joinA_img2 image_015_019
    (by decide) (by decide) (by decide)
    extract_joinA_pref2 extract_015_019
  unfold joinA_img3
  exact h
@[irreducible] def joinA_pref4 : String := joinA_pref3 ++ text_020_024
@[irreducible] def joinA_img4 : Array UInt16 := joinA_img3 ++ image_020_024
private theorem ws_joinA_pref4 : listEndsWS joinA_pref4.toList := by
  unfold joinA_pref4
  exact ws_cat joinA_pref3 text_020_024 ws_joinA_pref3 ws_text_020_024
theorem parse_joinA_pref4 :
    parseDecText joinA_pref4 = joinA_img4 := by
  have h := parse_append_eq joinA_pref3 text_020_024
    joinA_img3 image_020_024
    ws_joinA_pref3 parse_joinA_pref3 parse_020_024
  unfold joinA_pref4 joinA_img4
  exact h
theorem extract_joinA_pref4 :
    intfmtImage.extract 0 400 = joinA_img4 := by
  have h := extract_append_eq 0 320 400
    joinA_img3 image_020_024
    (by decide) (by decide) (by decide)
    extract_joinA_pref3 extract_020_024
  unfold joinA_img4
  exact h
@[irreducible] def joinA_pref5 : String := joinA_pref4 ++ text_025_029
@[irreducible] def joinA_img5 : Array UInt16 := joinA_img4 ++ image_025_029
private theorem ws_joinA_pref5 : listEndsWS joinA_pref5.toList := by
  unfold joinA_pref5
  exact ws_cat joinA_pref4 text_025_029 ws_joinA_pref4 ws_text_025_029
theorem parse_joinA_pref5 :
    parseDecText joinA_pref5 = joinA_img5 := by
  have h := parse_append_eq joinA_pref4 text_025_029
    joinA_img4 image_025_029
    ws_joinA_pref4 parse_joinA_pref4 parse_025_029
  unfold joinA_pref5 joinA_img5
  exact h
theorem extract_joinA_pref5 :
    intfmtImage.extract 0 480 = joinA_img5 := by
  have h := extract_append_eq 0 400 480
    joinA_img4 image_025_029
    (by decide) (by decide) (by decide)
    extract_joinA_pref4 extract_025_029
  unfold joinA_img5
  exact h
@[irreducible] def joinA_pref6 : String := joinA_pref5 ++ text_030_034
@[irreducible] def joinA_img6 : Array UInt16 := joinA_img5 ++ image_030_034
private theorem ws_joinA_pref6 : listEndsWS joinA_pref6.toList := by
  unfold joinA_pref6
  exact ws_cat joinA_pref5 text_030_034 ws_joinA_pref5 ws_text_030_034
theorem parse_joinA_pref6 :
    parseDecText joinA_pref6 = joinA_img6 := by
  have h := parse_append_eq joinA_pref5 text_030_034
    joinA_img5 image_030_034
    ws_joinA_pref5 parse_joinA_pref5 parse_030_034
  unfold joinA_pref6 joinA_img6
  exact h
theorem extract_joinA_pref6 :
    intfmtImage.extract 0 560 = joinA_img6 := by
  have h := extract_append_eq 0 480 560
    joinA_img5 image_030_034
    (by decide) (by decide) (by decide)
    extract_joinA_pref5 extract_030_034
  unfold joinA_img6
  exact h
@[irreducible] def joinA_pref7 : String := joinA_pref6 ++ text_035_039
@[irreducible] def joinA_img7 : Array UInt16 := joinA_img6 ++ image_035_039
private theorem ws_joinA_pref7 : listEndsWS joinA_pref7.toList := by
  unfold joinA_pref7
  exact ws_cat joinA_pref6 text_035_039 ws_joinA_pref6 ws_text_035_039
theorem parse_joinA_pref7 :
    parseDecText joinA_pref7 = joinA_img7 := by
  have h := parse_append_eq joinA_pref6 text_035_039
    joinA_img6 image_035_039
    ws_joinA_pref6 parse_joinA_pref6 parse_035_039
  unfold joinA_pref7 joinA_img7
  exact h
theorem extract_joinA_pref7 :
    intfmtImage.extract 0 640 = joinA_img7 := by
  have h := extract_append_eq 0 560 640
    joinA_img6 image_035_039
    (by decide) (by decide) (by decide)
    extract_joinA_pref6 extract_035_039
  unfold joinA_img7
  exact h
@[irreducible] def joinA_pref8 : String := joinA_pref7 ++ text_040_044
@[irreducible] def joinA_img8 : Array UInt16 := joinA_img7 ++ image_040_044
private theorem ws_joinA_pref8 : listEndsWS joinA_pref8.toList := by
  unfold joinA_pref8
  exact ws_cat joinA_pref7 text_040_044 ws_joinA_pref7 ws_text_040_044
theorem parse_joinA_pref8 :
    parseDecText joinA_pref8 = joinA_img8 := by
  have h := parse_append_eq joinA_pref7 text_040_044
    joinA_img7 image_040_044
    ws_joinA_pref7 parse_joinA_pref7 parse_040_044
  unfold joinA_pref8 joinA_img8
  exact h
theorem extract_joinA_pref8 :
    intfmtImage.extract 0 720 = joinA_img8 := by
  have h := extract_append_eq 0 640 720
    joinA_img7 image_040_044
    (by decide) (by decide) (by decide)
    extract_joinA_pref7 extract_040_044
  unfold joinA_img8
  exact h
@[irreducible] def joinA_pref9 : String := joinA_pref8 ++ text_045_049
@[irreducible] def joinA_img9 : Array UInt16 := joinA_img8 ++ image_045_049
private theorem ws_joinA_pref9 : listEndsWS joinA_pref9.toList := by
  unfold joinA_pref9
  exact ws_cat joinA_pref8 text_045_049 ws_joinA_pref8 ws_text_045_049
theorem parse_joinA_pref9 :
    parseDecText joinA_pref9 = joinA_img9 := by
  have h := parse_append_eq joinA_pref8 text_045_049
    joinA_img8 image_045_049
    ws_joinA_pref8 parse_joinA_pref8 parse_045_049
  unfold joinA_pref9 joinA_img9
  exact h
theorem extract_joinA_pref9 :
    intfmtImage.extract 0 800 = joinA_img9 := by
  have h := extract_append_eq 0 720 800
    joinA_img8 image_045_049
    (by decide) (by decide) (by decide)
    extract_joinA_pref8 extract_045_049
  unfold joinA_img9
  exact h
@[irreducible] def joinAText : String := joinA_pref9
@[irreducible] def joinAImage : Array UInt16 := joinA_img9
theorem parse_joinA : parseDecText joinAText = joinAImage := by
  unfold joinAText joinAImage
  exact parse_joinA_pref9
theorem extract_joinA :
    intfmtImage.extract 0 800 = joinAImage := by
  unfold joinAImage
  exact extract_joinA_pref9
theorem ws_joinA : listEndsWS joinAText.toList := by
  unfold joinAText
  exact ws_joinA_pref9

end IntFmt
