*** dumps/p4_16_samples/bfd_offload.p4/pruned/bfd_offload-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:57:56.972147600 +0200
--- dumps/p4_16_samples/bfd_offload.p4/pruned/bfd_offload-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:56.977376100 +0200
*************** BFD_Offload(16w32768) bfd_session_livene
*** 11,25 ****
      }
      bool on_tx(in bit<16> index) {
          bit<8> tmp_1;
-         bit<8> tmp_2;
-         bit<8> c;
          tmp_1 = this.getTx(index);
!         tmp_2 = tmp_1 + 8w1;
!         c = tmp_2;
!         if (c >= 8w4) 
              return true;
          else {
!             this.setTx(index, c);
              return false;
          }
      }
--- 11,21 ----
      }
      bool on_tx(in bit<16> index) {
          bit<8> tmp_1;
          tmp_1 = this.getTx(index);
!         if (tmp_1 + 8w1 >= 8w4) 
              return true;
          else {
!             this.setTx(index, tmp_1 + 8w1);
              return false;
          }
      }
