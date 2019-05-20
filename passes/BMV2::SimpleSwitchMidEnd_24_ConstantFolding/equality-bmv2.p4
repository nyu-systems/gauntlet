*** dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:58:16.186365700 +0200
--- dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:16.188970600 +0200
*************** control ingress(inout headers hdr, inout
*** 36,42 ****
              hdr.same.same = hdr.same.same | 8w4;
          tmp[0] = hdr.h;
          tmp[1] = hdr.a[0];
!         if (true && (!tmp[0].isValid() && !hdr.a[0].isValid() || tmp[0].isValid() && hdr.a[0].isValid() && tmp[0].s == hdr.a[0].s && tmp[0].v == hdr.a[0].v) && (!tmp[1].isValid() && !hdr.a[1].isValid() || tmp[1].isValid() && hdr.a[1].isValid() && tmp[1].s == hdr.a[1].s && tmp[1].v == hdr.a[1].v)) 
              hdr.same.same = hdr.same.same | 8w8;
      }
  }
--- 36,42 ----
              hdr.same.same = hdr.same.same | 8w4;
          tmp[0] = hdr.h;
          tmp[1] = hdr.a[0];
!         if ((!tmp[0].isValid() && !hdr.a[0].isValid() || tmp[0].isValid() && hdr.a[0].isValid() && tmp[0].s == hdr.a[0].s && tmp[0].v == hdr.a[0].v) && (!tmp[1].isValid() && !hdr.a[1].isValid() || tmp[1].isValid() && hdr.a[1].isValid() && tmp[1].s == hdr.a[1].s && tmp[1].v == hdr.a[1].v)) 
              hdr.same.same = hdr.same.same | 8w8;
      }
  }
