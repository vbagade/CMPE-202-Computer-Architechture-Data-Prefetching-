//Combined version of Larlsi and sandbox(brown)

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <list>
extern "C" {
#include "inc/prefetcher.h"
}

//Karsli defs

#define MAXDISTANCE 6 // max distance pointer
#define INTERVAL 512
#define TQSIZE 128
#define PFQSIZE 128
#define IP_MASK_8b (0x0ff)
#define IP_MASK_16b (0x0ffff)
#define IP_MASK_32b (0x0ffffffff)
#define TESTPERIOD 4*INTERVAL

//brown defs

#define PREFETCH_BUFFER_SIZE                64
#define L2_ACCESS_COUNT                        1024
#define LATENCY_AVERAGES                    32
#define LATENCY_AVERAGES_SHIFT                (unsigned short)log2(LATENCY_AVERAGES)
#define PREFETCHER_COUNT                    9

//karlsi testing related

int testblks = 0;
int testblks_hits = 0;
int otherblks = 0;
int otherblks_hits = 0;
int testing = 0;
int testperiod = TESTPERIOD;
int nexttest = TESTPERIOD;
int cntoff = 0;
int cnton = 0;
int DIFFLIMIT = INTERVAL*0.6;

//test queue for testing timeliness and relative success
typedef struct q{
  int tail;
  struct{
    unsigned long long int addr;
  }ent[TQSIZE];
}q_t;

//prefetch queue for prefetch filtering
typedef struct pq{
  int tail;
  struct{
    unsigned long long int addr;
  }ent[PFQSIZE];
}pq_t;
pq_t *pfq;


//Brown defs

class BasePrefetcher
{
    public:
        BasePrefetcher() {}
        virtual ~BasePrefetcher() {}
        virtual unsigned long long int predict(unsigned long long int pc,
                                               unsigned long long int address) = 0;
        virtual int getOffset() = 0;
};

class SequentialPrefetcher : public BasePrefetcher
{
    public:
        SequentialPrefetcher(int offset) : BasePrefetcher(),
                                           offset(offset) {}
        virtual ~SequentialPrefetcher() {}
        int getOffset() {return this->offset;};
        void setOffset(int offset) {this->offset = offset;};
        unsigned long long int predict(unsigned long long int pc,
                                       unsigned long long int address)
        {
            if(offset > 0)
                return (address + (offset * CACHE_LINE_SIZE));
            else
                return (address - ((offset * -1) * CACHE_LINE_SIZE));
        }
    protected:
        int offset;
};

// Prefetchers and resources (580 bits).
SequentialPrefetcher * prefetchers[PREFETCHER_COUNT];
unsigned long long int predictions[PREFETCHER_COUNT];            // 9 x 64 bits = 576 bits.
int primary;                                                    // 4 bits.

// Resources for calculuting average L2 to lower level memory
// access latency (898 bits).
std::list<unsigned short> mshrAddresses,                         // 16 bits of address + 1 valid bit each x 16 + 4 bits head index +
                                                                // 4 bits tail index = 280 bits
                          mshrCycles,                             // 16 bits of cycle each x 16 (head/tail index shared with cycles) = 256 bits
                          mshrLatencies;                        // 10 bits of cycle count each x 32 + 5 bits tail + 5 bits head = 330 bits
                                                                // (this could be implemented with less resources if needed).
unsigned short lastL2Access;                                    // 16 bits.
unsigned short averageLatencyCycles;                            // 16 bits.

// Sandbox and resources (240,138 bits bits).
std::list<unsigned short> sandbox[PREFETCHER_COUNT];            // 16 bits of address each x 1024 + 9 + 10 bits for index (shared
                                                                // with cyclesToArrival) x 9 = 147,546 bits.
std::list<unsigned short> cyclesToArrival[PREFETCHER_COUNT];    // 10 bits of cycles each x 1024 x 9 = 92,160 bits.
unsigned short sandboxScoreTotal[PREFETCHER_COUNT],                // 16 bits of score each x 9 = 144 bits.
                lateScoreTotal[PREFETCHER_COUNT],                // 16 bits of score each x 9 = 144 bits.
               usefulScoreTotal[PREFETCHER_COUNT];                // 16 bits of score each x 9 = 144 bits.

// Prefetch buffers (1036 bits).
std::list<unsigned short> prefetchBuffer;                        // 16 bits of address each x 64 + 10 bits index.


q_t *tq;
int tqhits = 0;
int avgtqhits = 0;
int tqmhits = 0;
unsigned long long int sumdiff = 0;
int l2acc = 0;
int l2miss = 0;
int high = 0;
int low = 0;
int pfcut = 0;
int pfcut2 = 0;
int low2 = 0;
int l2_mshr_limit = 8;
int distance = 1;
int pf_turn_on = 0;
int pf_turn_off = 0;


int dist[] = {0,1,2,3,4,5,6,7,8,9,10,11,12};
int dist_ptr = 1; // start with offset 1

bool filter(unsigned long long int baseAddress,
            unsigned long long int prefetchAddress)
{
    std::list<unsigned short>::iterator it;

    // Check if prefetch is in MSHR.
    for(it = mshrAddresses.begin(); it != mshrAddresses.end(); ++it)
    {
        if(*it == ((prefetchAddress >> 6) & 0xFFFF))
            return false;
    }
    // Check if prefetch is in prefetch buffer.
    for(it = prefetchBuffer.begin(); it != prefetchBuffer.end(); ++it)
    {
        if(*it == ((prefetchAddress >> 6) & 0xFFFF))
            return false;
    }
    // Check that the prefetch is in the same page as the base address.
    if((prefetchAddress >> 12) != (baseAddress >> 12))
    {
        return false;
    }
    // Check that the read queue isn't too full.
    else if(get_l2_read_queue_occupancy(0) > (L2_READ_QUEUE_SIZE - 6))
    {
        return false;
    }

    // If we got this far return true.
    return true;
}

void tq_ini(){

  int i;
  for(i=0;i<TQSIZE;i++){
    tq->ent[i].addr = 0;
  }
  tq->tail = -1;

}

int intq(unsigned long long int addr){

  int i;
  int found = 0;
  for(i=0;i<TQSIZE;i++){
    if(addr == tq->ent[i].addr){
      found = 1;
      break;
    }
  }
  return found;
}

void pfq_ini(){

  int i;
  for(i=0;i<PFQSIZE;i++){
    pfq->ent[i].addr = 0;
  }
  pfq->tail = -1;

}

int inpfq(unsigned long long int addr){
  int i;
  int found = 0;
  for(i=0;i<PFQSIZE;i++){
    if(addr == pfq->ent[i].addr){
      found = 1;
      break;
    }
  }
  return found;
}


void SEQT_ini(int low_bw){


  tq = (q_t *)malloc(sizeof(q_t));
  pfq = (pq_t *)malloc(sizeof(pq_t));
    if(low_bw) DIFFLIMIT = INTERVAL*0.5;
  tq_ini();
  pfq_ini();

}


void SEQT(unsigned long long int addr, unsigned long long int ip, int cache_hit){
 
  static int suml2occ = 0;
  static int numl2occhigh = 0;
 
  suml2occ +=  get_l2_mshr_occupancy(0);
 
  if(get_l2_mshr_occupancy(0)>=15)
    numl2occhigh++;
 
  unsigned long long int cycle = get_current_cycle(0);
  l2acc++;
  if(!cache_hit)
    l2miss++;
 
  //search for l2acc in tq
  int m;
  for(m=0; m<TQSIZE; m++){
    if(((addr&~0x3f) >> 6) == tq->ent[m].addr){
      tqhits++;

      if(!cache_hit)
    tqmhits++;
      
      break;
      
    }
  }
 
 
  if((l2acc%INTERVAL)==0){
    //decide on distance

    
    if(tqhits < 16){
      if(pfcut > 1){
    dist_ptr = 0;
    pfcut2 = 0;
      }
      else{
    if(dist_ptr > 1)
      dist_ptr--;
      }

      if((l2miss-tqmhits)>DIFFLIMIT)
    pfcut2++;
      else
    pfcut2 = 0;

      high = 0;
      low = 0;
      low2 = 0;
      pfcut++;
    }
    else{
      pfcut = 0;

      if(l2miss < 10){
    pfcut2 = 0;
      }
      else if((l2miss-tqmhits)>DIFFLIMIT){

    low2 = 0;

    if(pfcut2 > 1){
      dist_ptr = 0;
      pfcut2 = 0;
    }
    else{
      pfcut2++;

      if(dist_ptr == 0){
        if(pf_turn_on > 1){
          pf_turn_on = 0;
          dist_ptr = 1;
        }
        else
          pf_turn_on++;
      }

    }
    high = 0;
    low = 0;
      }
      else if((l2miss!=0) && (tqmhits !=0)){
    if((l2miss/tqmhits < 2)){
      
      if(low2>=2){
        if(dist_ptr<MAXDISTANCE){
          dist_ptr++;
          low2 = 0;
        }
      }
      else{
        low2++;
      }
    }
    else
      low2 = 0;

    high = 0;
    low = 0;
    pfcut2 = 0;
    
    
    if(dist_ptr == 0){
      if(pf_turn_on > 1){
        pf_turn_on = 0;
        dist_ptr = 1;
      }
      else
        pf_turn_on++;
    }
      }
      else{
    pfcut2 = 0;
    high = 0;
    low = 0;
    low2 = 0;

      }
    }

    distance = dist[dist_ptr];

    //reset table
    tq_ini();

    avgtqhits = 0;
    tqmhits = 0;
    sumdiff = 0;
    tqhits = 0;
    l2miss = 0;


    suml2occ = 0;
    numl2occhigh = 0;

    //testing related
    if(testing == 1){

      double tblks_hitrate = (double)testblks_hits/(double)testblks;
      double oblks_hitrate = (double)otherblks_hits/(double)otherblks;

      int pf_off = 0;

      if(knob_low_bandwidth){
    //turn off prefetching if really not worth it
    pf_off = ((double)oblks_hitrate < (1.2*(double)tblks_hitrate));

    if(pf_off == 0)
      pf_off = (otherblks_hits < 16);
      }
      else{
    // give advantage to prefetching
    pf_off = (((double)tblks_hitrate/(double)oblks_hitrate) > 1.2);

    if(pf_off == 0)
      pf_off = (otherblks_hits < 8);

      }

      int failedtest = ((testblks < 32) || (otherblks < 32));    


      if(!failedtest){
    if(pf_off){

      distance = 0;
      if(testperiod > INTERVAL)
        testperiod = testperiod>>1;
      
      //update turning off counter
      if(cntoff < 3)
        cntoff++;
      
      cnton = 0;
      
    }
    else{
      if(testperiod < (32*INTERVAL))
        testperiod = testperiod*2;
      
      //update turning off counter
      cntoff = 0;
      
      if(cnton < 3)
        cnton++;

    }
      }
      else{
    //failed test, try again next interval
    testperiod = INTERVAL;
      }
      nexttest += testperiod;
      
    }
    
    testing = 0;
    testblks_hits = 0;
    testblks = 0;
    otherblks_hits = 0;
    otherblks = 0;

  }

  //for now, do this only for low bandwidth
  if(l2acc==nexttest && knob_low_bandwidth){
    if(distance!=0)
      testing = 1;
    else
      nexttest += INTERVAL;
  }
 
  int Istblk = 0;

  if(testing == 1){

    
    //if keeps turning off prefetcher, increase the number of tblks
    /**/
    if(cntoff>=2)
      Istblk = (addr>>6)%3 != 1;
    else
      Istblk = (addr>>6)%4 == 2;



    if(Istblk){
      testblks++;

      if(cache_hit)
    testblks_hits++;
    }
    else{
      otherblks++;

      if(cache_hit)
    otherblks_hits++;
    }
    
  }


  unsigned long long int pf_address;

  pf_address = ((addr>>6)+distance)<<6;
  int samepage = (pf_address>>12) == (addr>>12);  

  //if distance is 0 (nopref), put in the queue as if distance = 1
  if(distance == 0)
    pf_address = ((addr>>6)+1)<<6;

  if(testing == 1){
    //if keeps turning off prefetcher, increase the number of tblks
    /**/
    if(cntoff>=2)
      Istblk = (pf_address>>6)%3 != 1;
    else
      Istblk = (pf_address>>6)%4 == 2;

   }


  int nopf = ((testing ==1) && (Istblk));
 
 
  if(!nopf){

    if(samepage && !inpfq(pf_address >> 6)){
      
      if(distance != 0){
    //todo: make occupancy limit check dynamic
    
    if(get_l2_mshr_occupancy(0) < l2_mshr_limit)
      {
        l2_prefetch_line(0, addr, pf_address, FILL_L2);
      }
    else
      {
        l2_prefetch_line(0, addr, pf_address, FILL_LLC);          
      }
        
    //add prefetched addr to the prefetch queue
    pfq->tail = (pfq->tail+1) % PFQSIZE;
    pfq->ent[pfq->tail].addr = (pf_address >> 6);
    
      }
      
    }
    
    
  }
 
 
    //add potential prefetch addr to the test queue
  if(samepage && !intq(pf_address>> 6)){
    tq->tail = (tq->tail+1) % TQSIZE;
    tq->ent[tq->tail].addr = (pf_address >> 6);
  }
 
 
 
} // end SEQT()


// *********************************************************************************************
// ************************************* ENDING OF SEQ **************************************
//**********************************************************************************************

//Sandbox related code

void l2_Sandbox_initialize(int cpu_num)
{  
    // Instantiate our prefetchers (-1 through +8, 9 in total).
    prefetchers[0] = new SequentialPrefetcher(-1);
    prefetchers[1] = new SequentialPrefetcher(1);
    prefetchers[2] = new SequentialPrefetcher(2);
    prefetchers[3] = new SequentialPrefetcher(3);
    prefetchers[4] = new SequentialPrefetcher(4);
    prefetchers[5] = new SequentialPrefetcher(5);
    prefetchers[6] = new SequentialPrefetcher(6);
    prefetchers[7] = new SequentialPrefetcher(7);
    prefetchers[8] = new SequentialPrefetcher(8);

    // The starting "old" last l2 access is the current cycle.
    lastL2Access = (unsigned short)(get_current_cycle(0) & 0xFFFF);

    // Set the starting average L2 to LLC/memory latency to 100 cycles.
    averageLatencyCycles = 100;

    // Set the best prefetcher indices to invalid.
    primary = -1;

    // Loop through the score registers clearing them.
    for(int pf = 0;  pf < PREFETCHER_COUNT; pf++)
        sandboxScoreTotal[pf] = lateScoreTotal[pf] = usefulScoreTotal[pf] = 0;
}

void l2_sandbox_operate(int cpu_num,
                           unsigned long long int addr,
                           unsigned long long int ip,
                           int cache_hit)
{
    std::list<unsigned short>::iterator sandboxIT,
                                        cyclesToArrivalIT;
    unsigned short elapsedCycles;
    bool scoresReady = false;

    //
    // Calculate how many cycles since the previous L2 access and then shift down the new
    // last L2 access.
    //
    elapsedCycles = (unsigned short)(get_current_cycle(0) & 0xFFFF) - lastL2Access;
    lastL2Access = (unsigned short)(get_current_cycle(0) & 0xFFFF);

    //
    // Check if the L2 access was a miss and update the user MSHR.
    //
    if(cache_hit == 0)
    {
        // Ensure it's not alrady in the MSHR.
        std::list<unsigned short>::iterator addressIT;
        for(addressIT = mshrAddresses.begin(); addressIT != mshrAddresses.end(); ++addressIT)
            // Break if we find the address.
            if(*addressIT == ((addr >> 6) & 0xFFFF))
                break;
        
        // If the iterator isn't pointing to the end it means it contains the address. If it is
        // then add the address and cycle to the lists.
        if(addressIT == mshrAddresses.end())
        {
            // Insert MISS address into our buffer. If there are too many entries then
            // remove the oldest.
            mshrAddresses.push_back((addr >> 6) & 0xFFFF);
            if(mshrAddresses.size() > L2_MSHR_COUNT)
                mshrAddresses.pop_front();

            // Insert the MISS address cycle (now) into our buffer. If there are too many
            // entries then remove the oldest.
            mshrCycles.push_back(get_current_cycle(0) & 0xFFFF);
            if(mshrCycles.size() > L2_MSHR_COUNT)
                mshrCycles.pop_front();
        }
    }

    //
    // Loop through the prefetchers updating which sandbox predictions have now
    // been filled and making new ones.
    //
    for(int pf = 0; pf < PREFETCHER_COUNT; pf++)
    {
        //
        // Loop through the predictions in the sandbox updating which predictions have "arrived" in
        // the L2 cache (i.e. cyclesToArrive reached zero).
        //
        cyclesToArrivalIT = cyclesToArrival[pf].begin();
        for(sandboxIT = sandbox[pf].begin(); sandboxIT != sandbox[pf].end(); ++sandboxIT)
        {
            // The arrival time value is the number of cycles left until the sandbox prediction would have been filled. This is based on
            // the average latency for L2 demand MISSes.
            if(*cyclesToArrivalIT > elapsedCycles)
                // If it still hasn't arrived then decrement the remaining cycles.
                *cyclesToArrivalIT -= elapsedCycles;
            else
                // The elapsed cycles is equal to or more than the reaminging cycles to arrival so
                // the prefetch has "arrived" in the L2 cache.
                *cyclesToArrivalIT = 0;
            
            // Increment our cycles to arrival list iterator.
            ++cyclesToArrivalIT;
        }

        //
        // Try and find the current cache access in the sandbox.
        //
        cyclesToArrivalIT = cyclesToArrival[pf].begin();
        for(sandboxIT = sandbox[pf].begin(); sandboxIT != sandbox[pf].end(); ++sandboxIT)
        {
            // Check if the L2 access address is in the sandbox for this prefetcher. If it is break
            // leaving the iterator pointed to it.
            if(((addr >> 6) & 0xFFFF) == *sandboxIT)
                break;

            // Increment our cycle list iterator.
            ++cyclesToArrivalIT;
        }
        
        //
        // Check if the iterator is pointing to past the end meaning that we looped through the entire
        // list and didn't find the entry.
        //
        if(sandboxIT != sandbox[pf].end())
        {
            // The score for the pure sandbox is the current latency in cycles. As in how many cycles are being
            // saved since this value was prefetched.
            sandboxScoreTotal[pf] += 1;

            // The tooLateScore is the remainging number of cycles until the prefetch would have been filled.
            if(*cyclesToArrivalIT > 0)
                lateScoreTotal[pf] += 1;
        }
    
        //
        // Check if the sandbox is full.
        //
        if(sandbox[pf].size() == L2_ACCESS_COUNT)
        {
            // Calculate final score.
            usefulScoreTotal[pf] = sandboxScoreTotal[pf] - lateScoreTotal[pf];

            // Clear sandbox and cycles to arrival lists.
            sandbox[pf].clear();
            cyclesToArrival[pf].clear();

            // Mark the evaluation period over.
            scoresReady = true;
        }

        //
        // Have the prefetcher make a sandbox prediction and enter the average latency in cycles
        // into the arrival time buffer. If we have over L2_ACCESS_COUNT entries in either then remove
        // the oldest entries.
        //        
        predictions[pf] = prefetchers[pf]->predict(ip, addr);

        // Insert prediction into the sandbox.
        sandbox[pf].push_back((predictions[pf] >> 6) & 0xFFFF);
        if(sandbox[pf].size() > L2_ACCESS_COUNT)
            sandbox[pf].pop_front();

        // If the value was over our limit (1024) then max it out.
        if(averageLatencyCycles > 0x3FF)
            cyclesToArrival[pf].push_back(0x3FF);
        else
            cyclesToArrival[pf].push_back(averageLatencyCycles & 0x3FF);
        if(cyclesToArrival[pf].size() > L2_ACCESS_COUNT)
            cyclesToArrival[pf].pop_front();
    }

    //
    // If we have new scores calculated then pick the primary prefetcher.
    //
    if(scoresReady == true)
    {
        // Find the primary (optimal distance) prefetcher.
        primary = -1;
        for(int pf = 0; pf < PREFETCHER_COUNT; pf++)
        {
            // Save potential new best prefetcher.
            if(primary == -1 || usefulScoreTotal[pf] > usefulScoreTotal[primary])
                primary = pf;
        }

        // Thresholds to decide if the scores are good enough to prefetch.
        if(sandboxScoreTotal[primary] < ((L2_ACCESS_COUNT >> 2) * 1))
            primary = -1;

        // Clear scores.
        for(int pf = 0; pf < PREFETCHER_COUNT; pf++)
            sandboxScoreTotal[pf] = lateScoreTotal[pf] = usefulScoreTotal[pf] = 0;
    }

    //
    // Ensure the primary prefetcher is valid.
    //
    if(primary != -1)
    {
        // Filter the prediction. If it returns true we can proceed.
        if(filter(addr, predictions[primary]) == true)
        {
            // Check MSHR occupancy level (greater than half occupancy).
            if(get_l2_mshr_occupancy(0) > (L2_MSHR_COUNT >> 1))
            {
                // Prefetch into the LLC (L3) because MSHRs are scarce.
                if(l2_prefetch_line(0, addr, predictions[primary], FILL_LLC) == 1)
                {
                    // Add to prefetch buffer.
                    prefetchBuffer.push_back((predictions[primary] >> 6) & 0xFFFF);
                    if(prefetchBuffer.size() > PREFETCH_BUFFER_SIZE)
                        prefetchBuffer.pop_front();
                }
            }
            else
            {
                // MSHRs not too busy, so prefetch into L2.
                  if(l2_prefetch_line(0, addr, predictions[primary], FILL_L2) == 1)
                {
                    // If we were successful at issuing the prefetch then add the address to our
                    // global prefetch buffer.
                    prefetchBuffer.push_back((predictions[primary] >> 6) & 0xFFFF);
                    if(prefetchBuffer.size() > PREFETCH_BUFFER_SIZE)
                        prefetchBuffer.pop_front();
                }
            }
        }
    }
}


void l2_sandbox_cache_fill(int cpu_num, unsigned long long int addr, int set, int way, int prefetch, unsigned long long int evicted_addr)
{    
    // Iterators.
    std::list<unsigned short>::iterator addressIT,
                                          cycleIT,
                                        averageIT;

    //
    // Loop through MSHR address buffer looking for the filled address.
    //
    cycleIT = mshrCycles.begin();
    for(addressIT = mshrAddresses.begin(); addressIT != mshrAddresses.end(); ++addressIT)
    {
        // Check if the current iterator address is equal to the filled address.
        if(*addressIT == ((addr >> 6) & 0xFFFF))
        {    
            // Calculate the number of cycles between when the demand MISS occured and when it was
            // filled (now). This is the instantaneous latency so add it to the buffer.
            mshrLatencies.push_back(((get_current_cycle(0) & 0xFFFF) - *cycleIT) & 0x3FF);
            if(mshrLatencies.size() > LATENCY_AVERAGES)
                mshrLatencies.pop_front();

            // Since the address and it's corresponding cycle have been filled we remove
            // them from our lists.
            mshrAddresses.erase(addressIT);
            mshrCycles.erase(cycleIT);

            // Check if the latency buffer is full and an average can be calculated.
            if(mshrLatencies.size() == LATENCY_AVERAGES)
            {
                // Clear the old average latency.
                averageLatencyCycles = 0;

                // Loop through the latency buffer summing the latencies.
                for(averageIT = mshrLatencies.begin(); averageIT != mshrLatencies.end(); ++averageIT)
                {
                    // Add the cycle count.
                    averageLatencyCycles += *averageIT;
                }

                // Calculate new average latency.
                averageLatencyCycles = averageLatencyCycles >> LATENCY_AVERAGES_SHIFT;
            }

            // We found the address so break out of the loop.
            break;
        }
        ++cycleIT;
    }
}



// *********************************************************************************************
// ******************************* BEGINNING OF IP STRIDE **************************************
//**********************************************************************************************

#define IP_TRACKER_COUNT 1024
#define IP_PREFETCH_DEGREE 1
#define IP_DISTANCE 2

typedef struct ip_tracker
{
  // the IP we're tracking
  unsigned int ip;//32 bits

  // the last address accessed by this IP
  unsigned short last_addr;//16 bits
  // the stride between the last two addresses accessed by this IP
  short last_stride;//8 bits

  // use LRU to evict old IP trackers
  unsigned long long int lru_cycle;
} ip_tracker_t;

ip_tracker_t trackers[IP_TRACKER_COUNT];


void IP_STRIDE_ini() {
  int i;
  for(i=0; i<IP_TRACKER_COUNT; i++)
    {
      trackers[i].ip = 0;
      trackers[i].last_addr = 0;
      trackers[i].last_stride = 0;
      trackers[i].lru_cycle = 0;
    }
}

void IP_STRIDE(unsigned long long int addr, unsigned long long int ip, int cache_hit) {
  // check for a tracker hit
  int tracker_index = -1;
  unsigned long long int addr_blk = addr >> 6;

  int i;
  for(i=0; i<IP_TRACKER_COUNT; i++)
    {
      if(trackers[i].ip == (ip & IP_MASK_32b))
    {
      trackers[i].lru_cycle = get_current_cycle(0);
      tracker_index = i;
      break;
    }
    }

  if(tracker_index == -1)
    {
      // this is a new IP that doesn't have a tracker yet, so allocate one
      int lru_index=0;
      unsigned long long int lru_cycle = trackers[lru_index].lru_cycle;
      int i;
      for(i=0; i<IP_TRACKER_COUNT; i++)
    {
      if(trackers[i].lru_cycle < lru_cycle)
        {
          lru_index = i;
          lru_cycle = trackers[lru_index].lru_cycle;
        }
    }

      tracker_index = lru_index;

      // reset the old tracker
      trackers[tracker_index].ip = ip & IP_MASK_32b;
      trackers[tracker_index].last_addr = addr_blk & IP_MASK_16b;
      trackers[tracker_index].last_stride = 0;
      trackers[tracker_index].lru_cycle = get_current_cycle(0);

      return;
    }

  // calculate the stride between the current address and the last address
  // this bit appears overly complicated because we're calculating
  // differences between unsigned address variables
  short stride = 0;
  if((addr_blk & IP_MASK_16b) > trackers[tracker_index].last_addr)
    {
      stride = ((addr_blk & IP_MASK_16b) - trackers[tracker_index].last_addr) & IP_MASK_8b;
    }
  else
    {
      stride = (trackers[tracker_index].last_addr - (addr_blk & IP_MASK_16b)) & IP_MASK_8b;
      stride *= -1;
    }

  // don't do anything if we somehow saw the same address twice in a row
  if(stride == 0)
    {
      return;
    }

  // only do any prefetching if there's a pattern of seeing the same
  // stride more than once
  if(stride == trackers[tracker_index].last_stride)
    {
      // do some prefetching
      int i;
      int tempdist = distance;
      tempdist = tempdist / 2;
      if (tempdist == 0) tempdist = 1;
      for(i=tempdist; i<IP_PREFETCH_DEGREE+tempdist; i++)
      //for(i=IP_DISTANCE; i<IP_PREFETCH_DEGREE+IP_DISTANCE; i++)
    {
      unsigned long long int pf_address = (addr_blk + (stride*(i+1))) << 6;

      // only issue a prefetch if the prefetch address is in the same 4 KB page
      // as the current demand access address
      if((pf_address>>12) != (addr>>12))
        {
          break;
        }

      // check the MSHR occupancy to decide if we're going to prefetch to the L2 or LLC
      if (!inpfq((pf_address >> 6))) {
      if(get_l2_mshr_occupancy(0) < l2_mshr_limit)
        {
          l2_prefetch_line(0, addr, pf_address, FILL_L2);
        }
      else
        {
          l2_prefetch_line(0, addr, pf_address, FILL_LLC);
        }
         pfq->tail = (pfq->tail+1) % PFQSIZE;
        pfq->ent[pfq->tail].addr = (pf_address >> 6);
      }
      
    }
    }

  trackers[tracker_index].last_addr = addr_blk & IP_MASK_16b;
  trackers[tracker_index].last_stride = stride;
}

// *********************************************************************************************
// ************************************* END OF IP STRIDE **************************************
//**********************************************************************************************


void l2_prefetcher_initialize(int cpu_num)
{
  l2_Sandbox_initialize(cpu_num);  
  SEQT_ini(knob_low_bandwidth);
}


void l2_prefetcher_operate(int cpu_num, unsigned long long int addr, unsigned long long int ip, int cache_hit)
{
  l2_sandbox_operate(cpu_num,addr,ip,cache_hit);
  SEQT(addr, ip, cache_hit);  
}

void l2_cache_fill(int cpu_num, unsigned long long int addr, int set, int way, int prefetch, unsigned long long int evicted_addr)
{

}

void l2_prefetcher_heartbeat_stats(int cpu_num)
{

}
void l2_prefetcher_warmup_stats(int cpu_num)
{

}

void l2_prefetcher_final_stats(int cpu_num)
{

}
