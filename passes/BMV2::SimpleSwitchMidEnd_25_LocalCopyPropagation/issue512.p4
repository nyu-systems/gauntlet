*** dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:17.367280400 +0200
--- dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:17.369765800 +0200
*************** parser parserI(packet_in pkt, out Parsed
*** 25,53 ****
      }
  }
  control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
-     bool hasReturned_0;
-     bool cond;
      bool pred;
-     bool cond_0;
-     bool pred_0;
      @name("cIngress.foo") action foo_0() {
-         hasReturned_0 = false;
          meta.b = meta.b + 4w5;
          {
              {
!                 cond = meta.b > 4w10;
!                 pred = cond;
                  {
!                     meta.b = (pred ? meta.b ^ 4w5 : meta.b);
!                     hasReturned_0 = (pred ? true : hasReturned_0);
                  }
              }
          }
          {
              {
!                 cond_0 = !hasReturned_0;
!                 pred_0 = cond_0;
!                 meta.b = (pred_0 ? meta.b + 4w5 : meta.b);
              }
          }
      }
--- 25,44 ----
      }
  }
  control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
      bool pred;
      @name("cIngress.foo") action foo_0() {
          meta.b = meta.b + 4w5;
          {
              {
!                 pred = meta.b > 4w10;
                  {
!                     meta.b = (meta.b > 4w10 ? meta.b ^ 4w5 : meta.b);
                  }
              }
          }
          {
              {
!                 meta.b = (!(pred ? true : false) ? meta.b + 4w5 : meta.b);
              }
          }
      }
