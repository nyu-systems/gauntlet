*** dumps/p4_16_samples/serenum.p4/pruned/serenum-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-05-20 17:00:20.878687500 +0200
--- dumps/p4_16_samples/serenum.p4/pruned/serenum-BMV2::SimpleSwitchMidEnd_9_ConstantFolding.p4	2019-05-20 17:00:20.881184900 +0200
*************** control c(inout Headers h) {
*** 28,34 ****
              if (h.eth.type == 16w0x800) 
                  h.eth.setInvalid();
              else 
!                 h.eth.type = (bit<16>)16w0;
      }
  }
  parser p<H>(packet_in _p, out H h);
--- 28,34 ----
              if (h.eth.type == 16w0x800) 
                  h.eth.setInvalid();
              else 
!                 h.eth.type = 16w0;
      }
  }
  parser p<H>(packet_in _p, out H h);
