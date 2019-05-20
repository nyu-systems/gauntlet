*** dumps/p4_16_samples/issue648.p4/pruned/issue648-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 16:59:23.651336400 +0200
--- dumps/p4_16_samples/issue648.p4/pruned/issue648-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-05-20 16:59:23.655359700 +0200
*************** header hdr {
*** 6,13 ****
  }
  control ingress(inout hdr h) {
      apply {
!         h.a[7:0] = ((bit<32>)h.c)[7:0];
!         h.a[15:8] = (h.c + h.c)[7:0];
      }
  }
  control c(inout hdr h);
--- 6,13 ----
  }
  control ingress(inout hdr h) {
      apply {
!         h.a = h.a & ~32w0xff | (bit<32>)((bit<32>)h.c)[7:0] << 0 & 32w0xff;
!         h.a = h.a & ~32w0xff00 | (bit<32>)(h.c + h.c)[7:0] << 8 & 32w0xff00;
      }
  }
  control c(inout hdr h);
