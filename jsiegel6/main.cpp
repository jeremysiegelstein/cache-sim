#include <stdlib.h>
#include <stdio.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <map>
#include <math.h>
#include <climits>

#define KB 1024
#define LINE_SIZE 32

using namespace std;

void directMap(vector<unsigned long> addresses, int size, long *hits, long *accesses){
    int total = size * KB;
    int numLines = total/LINE_SIZE;
    long *cache = new long[numLines];
    int index;
    long tag;
    *hits = 0;
    *accesses = 0;
    for(unsigned long i = 0; i < addresses.size(); i++){
        index = (addresses[i] >> 5) % numLines;
        tag = addresses[i]/total;

        if(cache[index] == tag) *hits = *hits + 1;
        else{
            cache[index] = tag;
        }
        *accesses = *accesses + 1;
    }
    delete [] cache;
}

void setAssociative(vector<unsigned long> addresses, int ways, long *hits, long *accesses){
    int total = 16 * KB;
    int numLines = total/LINE_SIZE;
    int sets = numLines/ways;
    int index;
    long tag;
    long **cache = new long*[sets];
    map<long, long> LRU;
    long least_recent;
    long to_replace;
    int way;
    *hits = 0;
    *accesses = 0;
    for(long i = 0; i < numLines; i++){
        LRU[i] = -1;
    }
    for(int i = 0; i < sets; i++){
        cache[i] = new long[ways];
    }

    for(unsigned long i = 0; i < addresses.size(); i++){
        index = (addresses[i] >> 5) % sets;
        tag = addresses[i]/(sets * LINE_SIZE);
        int j;
        *accesses = *accesses + 1;
        for(j = 0; j < ways; j++){
            if(cache[index][j] == tag){
                LRU[(index * ways) + j] = *accesses;
                *hits = *hits + 1;
                break;
            }
        }
        //If we miss
        if( j == ways){
            least_recent = INT_MAX;
            for(int k = 0; k < ways; k++){
                if(LRU[(index * ways) + k] < least_recent){
                    least_recent = LRU[(index * ways) + k];
                    to_replace = (index * ways) + k;
                    way = k;
                }
            }
            LRU[to_replace] = *accesses;
            cache[index][way] = tag;
        }
    }

    for(int i = 0; i < sets; i++){
        delete [] cache[i];
    }
    delete [] cache;
    LRU.clear();
}

void fullyAssociativeLRU(vector<unsigned long> addresses, long *hits, long *accesses){
    int total = 16 * KB;
    int numLines = total/LINE_SIZE;

    long *cache = new long[numLines];
    *hits = 0;
    *accesses = 0;
    long tag;
    map<long, long> LRU;
    long least_recent;
    long to_replace;
    //Initialized each initial most recent access to -1
    for(long i = 0; i < numLines; i++){
        LRU[i] = -1;
    }
    for(unsigned long i = 0; i < addresses.size(); i++){
        *accesses = *accesses + 1;
        tag = addresses[i]/LINE_SIZE;
        int j;

        for(j = 0; j < numLines; j++){
            if(tag == cache[j]){
                //Cache hit
                LRU[j] = *accesses;
                *hits = *hits + 1;
                break;
            }
        }
        if(j == numLines){
            //Cache Miss
            least_recent = INT_MAX;
            for(int k = 0; k < numLines; k++){
                if(LRU[k] < least_recent){
                    least_recent = LRU[k];
                    to_replace = k;
                }
            }
            LRU[to_replace] = *accesses;
            cache[to_replace] = tag;
        }
    }
    delete [] cache;
    LRU.clear();
}

void fullyAssociativeHotCold(vector<unsigned long> addresses, long *hits, long *accesses){
    int total = 16 * KB;
    int numLines = total/LINE_SIZE;

    long *hotCold = new long[numLines];
    long *cache = new long[numLines];
    *hits = 0;
    *accesses = 0;
    long tag;
    int victim = 0;

    for(long i = 0; i < numLines; i++){
        hotCold[i] = 0;
    }
    for(unsigned long i = 0; i < addresses.size(); i++){
        *accesses = *accesses + 1;
        tag = addresses[i]/LINE_SIZE;
        int j;

        for(j = 0; j < numLines; j++){
            if(tag == cache[j]){
                //Cache hit
                int parent  = 0;
                for(int k = 0; k < (int)log2(numLines); k++){
                    int old = (j/(numLines / (2 << k))) % 2;

                    if(old == 0){
                        hotCold[parent] = 1;
                        parent = (2 * parent) + 1;
                    }
                    else{
                        hotCold[parent] = 0;
                        parent = 2 * (parent + 1);
                    }
                }
                *hits = *hits + 1;
                break;
            }
        }
        if(j == numLines){
            //Cache Miss
            victim = 0;
            for(int k = 0; k < (int)log2(numLines); k++){

                if(hotCold[victim] == 0){
                    hotCold[victim] = 1;
                    victim = (2 * victim) + 1;
                }
                else{
                    hotCold[victim] = 0;
                    victim = 2 * (victim + 1);
                }
            }
            victim = victim + 1 - numLines;
            cache[victim] = tag;
        }
    }

    delete [] hotCold;
    delete [] cache;
}

void setAssociativeNoWrite(vector<unsigned long> addresses, vector<string> readWrite, int ways, long *hits, long *accesses){
    int total = 16 * KB;
    int numLines = total/LINE_SIZE;
    int sets = numLines/ways;
    int index;
    long tag;
    long **cache = new long*[sets];
    map<long, long> LRU;
    long least_recent;
    long to_replace;
    int way;
    *hits = 0;
    *accesses = 0;
    for(long i = 0; i < numLines; i++){
        LRU[i] = -1;
    }
    for(long i = 0; i < sets; i++){
        cache[i] = new long[ways];
    }
    *hits = 0;
    *accesses = 0;
    for(unsigned long i = 0; i < addresses.size(); i++){
        index = (addresses[i] >> 5) % sets;
        tag = addresses[i]/(sets * LINE_SIZE);
        int j;
        *accesses = *accesses + 1;
        for(j = 0; j < ways; j++){
            if(cache[index][j] == tag){
                *hits = *hits + 1;
                LRU[(index * ways) + j] = *accesses;
                break;
            }
        }
        //If we miss and it's a load
        if( j == ways && readWrite[i] == "L"){
            least_recent = INT_MAX;
            for(int k = 0; k < ways; k++){
                if(LRU[(index * ways) + k] < least_recent){
                    least_recent = LRU[(index * ways) + k];
                    to_replace = (index * ways) + k;
                    way = k;
                }
            }
            LRU[to_replace] = *accesses;
            cache[index][way] = tag;
        }
    }

    for(int i = 0; i < sets; i++){
        delete [] cache[i];
    }
    delete [] cache;
    LRU.clear();
}

void prefetch(vector<unsigned long> addresses, int ways, long *hits, long *accesses){
    int total = 16 * KB;
    int numLines = total/LINE_SIZE;
    int sets = numLines/ways;
    int index;
    int pre_index;
    long tag;
    long pre_tag;
    long **cache = new long*[sets];
    map<long, long> LRU;
    long least_recent;
    long to_replace;
    int way;
    *hits = 0;
    *accesses = 0;
    int recent = 0;
    for(long i = 0; i < numLines; i++){
        LRU[i] = -1;
    }
    for(int i = 0; i < sets; i++){
        cache[i] = new long[ways];
    }
    for(unsigned long i = 0; i < addresses.size(); i++){
        index = (addresses[i] >> 5) % sets;
        tag = addresses[i]/(sets * LINE_SIZE);
        pre_index = (index + 1) % sets;
        pre_tag = (addresses[i] + LINE_SIZE)/(sets * LINE_SIZE);
        int j;
        int l;
        *accesses = *accesses + 1;
        recent++;
        for(j = 0; j < ways; j++){
            if(cache[index][j] == tag){
                //Cache hit
                LRU[(index * ways) + j] = recent;
                *hits = *hits + 1;
                break;
            }
        }

        //If cache miss
        if( j == ways){
            least_recent = INT_MAX;
            for(int k = 0; k < ways; k++){
                if(LRU[(index * ways) + k] < least_recent){
                    least_recent = LRU[(index * ways) + k];
                    to_replace = (index * ways) + k;
                    way = k;
                }
            }
            LRU[to_replace] = recent;
            cache[index][way] = tag;
        }

        recent++;
        for(l = 0; l < ways; l++){
            if(cache[pre_index][l] == pre_tag){
                //Prefetch hit
                LRU[(pre_index * ways) + l] = recent;
                break;
            }
        }
        if(l == ways){
            //Prefetch miss
            least_recent = INT_MAX;
            for(int k = 0; k < ways; k++){
                if(LRU[(pre_index * ways) + k] < least_recent){
                    least_recent = LRU[(pre_index * ways) + k];
                    to_replace = (pre_index * ways) + k;
                    way = k;
                }
            }
            LRU[to_replace] = recent;
            cache[pre_index][way] = pre_tag;
        }
    }

    for(int i = 0; i < sets; i++){
        delete [] cache[i];
    }
    delete [] cache;
    LRU.clear();
}

void prefetchOnMiss(vector<unsigned long> addresses, int ways, long *hits, long *accesses){
    int total = 16 * KB;
    int numLines = total/LINE_SIZE;
    int sets = numLines/ways;
    int index;
    int pre_index;
    long tag;
    long pre_tag;
    long **cache = new long*[sets];
    map<long, long> LRU;
    long least_recent;
    long to_replace;
    int way;
    *hits = 0;
    *accesses = 0;
    int recent = 0;
    for(long i = 0; i < numLines; i++){
        LRU[i] = -1;
    }
    for(int i = 0; i < sets; i++){
        cache[i] = new long[ways];
    }
    for(unsigned long i = 0; i < addresses.size(); i++){
        index = (addresses[i] >> 5) % sets;
        tag = addresses[i]/(sets * LINE_SIZE);
        pre_index = (index + 1) % sets;
        pre_tag = (addresses[i] + LINE_SIZE)/(sets * LINE_SIZE);
        int j;
        int l;
        *accesses = *accesses + 1;
        recent++;
        for(j = 0; j < ways; j++){
            if(cache[index][j] == tag){
                //Cache hit
                LRU[(index * ways) + j] = recent;
                *hits = *hits + 1;
                break;
            }
        }

        //If cache miss
        if( j == ways){
            least_recent = INT_MAX;
            for(int k = 0; k < ways; k++){
                if(LRU[(index * ways) + k] < least_recent){
                    least_recent = LRU[(index * ways) + k];
                    to_replace = (index * ways) + k;
                    way = k;
                }
            }
            LRU[to_replace] = recent;
            cache[index][way] = tag;

            recent++;
            for(l = 0; l < ways; l++){
                if(cache[pre_index][l] == pre_tag){
                    //Prefetch hit
                    LRU[(pre_index * ways) + l] = recent;
                    break;
                }
            }
            if(l == ways){
                //Prefetch miss
                least_recent = INT_MAX;
                for(int k = 0; k < ways; k++){
                    if(LRU[(pre_index * ways) + k] < least_recent){
                        least_recent = LRU[(pre_index * ways) + k];
                        to_replace = (pre_index * ways) + k;
                        way = k;
                    }
                }
                LRU[to_replace] = recent;
                cache[pre_index][way] = pre_tag;
            }
        }
    }

    for(int i = 0; i < sets; i++){
        delete [] cache[i];
    }
    delete [] cache;
    LRU.clear();
}

int main(int argc, char **argv){
    string in;
    string out;

    if(argc == 3){
        in = argv[1];
        out = argv[2];
    }
    else{
        cerr << "Incorrect number of command line arguments" << endl;
        exit(1);
    }

    vector<unsigned long> addresses;
    unsigned long address;
    //readWrite vector used only for (4) (Set associative cache with no allocation on a write miss)
    vector<string> readWrite;
    string type;
    ifstream infile(in);

    while(true){
        infile >> type >> hex >> address;
        if(infile.eof()) break;
        addresses.push_back(address);
        readWrite.push_back(type);
    }
    infile.close();

    ofstream outfile(out);

    long hits = 0;
    long accesses = 0;

    for(int i = 1; i < 32; i*=4){
        directMap(addresses, i, &hits, &accesses);
        outfile << hits << "," << accesses << "; ";
    }
    directMap(addresses, 32, &hits, &accesses);
    outfile << hits << "," << accesses << ";" << endl;

    for(int i = 2; i < 16; i *= 2){
        setAssociative(addresses, i, &hits, &accesses);
        outfile << hits << "," << accesses << "; ";
    }
    setAssociative(addresses, 16, &hits, &accesses);
    outfile << hits << "," << accesses << ";" << endl;

    fullyAssociativeLRU(addresses, &hits, &accesses);
    outfile << hits << "," << accesses << ";" << endl;

    fullyAssociativeHotCold(addresses, &hits, &accesses);
    outfile << hits << "," << accesses << ";" << endl;

    for(int i = 2; i < 16; i *= 2){
        setAssociativeNoWrite(addresses, readWrite, i, &hits, &accesses);
        outfile << hits << "," << accesses << "; ";
    }
    setAssociativeNoWrite(addresses, readWrite, 16, &hits, &accesses);
    outfile << hits << "," << accesses << ";" << endl;

    for(int i = 2; i < 16; i *= 2){
        prefetch(addresses, i, &hits, &accesses);
        outfile << hits << "," << accesses << "; ";
    }
    prefetch(addresses, 16, &hits, &accesses);
    outfile << hits << "," << accesses << ";" << endl;

    for(int i = 2; i < 16; i *= 2){
        prefetchOnMiss(addresses, i, &hits, &accesses);
        outfile << hits << "," << accesses << "; ";
    }
    prefetchOnMiss(addresses, 16, &hits, &accesses);
    outfile << hits << "," << accesses << ";" << endl;

    outfile.close();
}
