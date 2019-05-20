*** dumps/p4_16_samples/serenum.p4/pruned/serenum-BMV2::SimpleSwitchMidEnd_1_EliminateNewtype.p4	2019-05-20 17:00:20.801870200 +0200
--- dumps/p4_16_samples/serenum.p4/pruned/serenum-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:00:20.832211000 +0200
***************
*** 1,17 ****
  #include <core.p4>
- enum bit<16> EthTypes {
-     IPv4 = 16w0x800,
-     ARP = 16w0x806,
-     RARP = 16w0x8035,
-     EtherTalk = 16w0x809b,
-     VLAN = 16w0x8100,
-     IPX = 16w0x8137,
-     IPv6 = 16w0x86dd
- }
  header Ethernet {
!     bit<48>  src;
!     bit<48>  dest;
!     EthTypes type;
  }
  struct Headers {
      Ethernet eth;
--- 1,8 ----
  #include <core.p4>
  header Ethernet {
!     bit<48> src;
!     bit<48> dest;
!     bit<16> type;
  }
  struct Headers {
      Ethernet eth;
*************** parser prs(packet_in p, out Headers h) {
*** 21,28 ****
      state start {
          p.extract<Ethernet>(e);
          transition select(e.type) {
!             EthTypes.IPv4: accept;
!             EthTypes.ARP: accept;
              default: reject;
          }
      }
--- 12,19 ----
      state start {
          p.extract<Ethernet>(e);
          transition select(e.type) {
!             16w0x800: accept;
!             16w0x806: accept;
              default: reject;
          }
      }
*************** control c(inout Headers h) {
*** 33,42 ****
          if (!h.eth.isValid()) 
              hasReturned_0 = true;
          if (!hasReturned_0) 
!             if (h.eth.type == EthTypes.IPv4) 
                  h.eth.setInvalid();
              else 
!                 h.eth.type = (EthTypes)16w0;
      }
  }
  parser p<H>(packet_in _p, out H h);
--- 24,33 ----
          if (!h.eth.isValid()) 
              hasReturned_0 = true;
          if (!hasReturned_0) 
!             if (h.eth.type == 16w0x800) 
                  h.eth.setInvalid();
              else 
!                 h.eth.type = (bit<16>)16w0;
      }
  }
  parser p<H>(packet_in _p, out H h);
