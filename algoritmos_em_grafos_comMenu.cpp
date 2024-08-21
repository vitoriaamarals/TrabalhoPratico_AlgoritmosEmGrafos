/* 

        TRABALHO PRÁTICO
        DISCIPLINA: GCC218 - ALGORITMOS EM GRAFOS

        ALUNOS:
            FELIPE CRISOSTOMO SILVA OLIVEIRA - 202220937
            MARIA EDUARDA FERREIRA DA SILVA - 202310419
            VITÓRIA CHRISTIE AMARAL SANTOS - 202310422

        TURMA: 10A

*/


#include <iostream>
#include <vector>
#include <stack>
#include <queue>
#include <algorithm>
#include <limits> 
#include <set>
#include <sstream>

using namespace std;

class UFDS {
private:

    vector<int> pai;
    vector<int> rank; //vetor que armazena a aproximação da altura da árvore

public:

    //construtor com n conjuntos disjuntos
    UFDS(int n) {
        pai.resize(n);
        rank.resize(n, 0);
        for (int i = 0; i < n; ++i) {
            pai[i] = i;
        }
    }

    //Dado um elemento do conjunto, busca-se seu pai no conjunto disjunto e o 
    //atualiza (se necessário) para o ancestral de maior nivel na arvore.
    int encontrar(int x) {
        if (pai[x] != x) {
            pai[x] = encontrar(pai[x]); 
        }
        return pai[x];
    }

    /* Dados dois elementos, une os seus respectivos conjuntos considerando o rank 
      de maior valor*/
    void unionSet(int x, int y) {
        int raizX = encontrar(x);
        int raizY = encontrar(y);

        if (raizX != raizY) {
            if (rank[raizX] > rank[raizY]) {
                pai[raizY] = raizX;
            } else if (rank[raizX] < rank[raizY]) {
                pai[raizX] = raizY;
            } else {
                pai[raizY] = raizX;
                ++rank[raizX];
            }
        }
    }

    //dados dois elementos no conjunto, verifica se eles possuem o mesmo pai
    bool mesmoConjunto(int x, int y) {
        return encontrar(x) == encontrar(y);
    }

};

class Grafo {
private:

    int vertices; //número de vértices
    bool direcionado; //indica se o grafo é direcionado ou não
    vector<vector<vector<int>>> adj_list; // lista de adjacência do grafo original: [vértice, peso, id_aresta]
    vector<vector<int>> adj_list_transposto; // Grafo transposto
    vector<pair<int, pair<int, int>>> arestas; //par representado por peso da aresta e vertice inicial e final

public:

    Grafo() : vertices(0), direcionado(false) {}

    // Construtor que inicializa o grafo com um número de vértices e um indicador de se ele é direcionado
    Grafo(int vertices, bool direcionado)
        : vertices(vertices), direcionado(direcionado) {
        adj_list.resize(vertices); //redimensiona a lista de adjacencia para o número de vértices
        adj_list_transposto.resize(vertices); // redimensiona a lista de adjacencia do grafo transposto
    }

    void adicionarAresta(int id_aresta, int u, int v, int peso) {
        adj_list[u].push_back({v, peso, id_aresta}); //// Adiciona a aresta (v, peso, id_aresta) à lista de adjacência de u
        adj_list_transposto[v].push_back(u); // Adiciona a aresta inversa no grafo transposto

        //se o grafo é não direcionado, adiciona a aresta inversa também
        if (!direcionado) {
            adj_list[v].push_back({u, peso, id_aresta});
            adj_list_transposto[u].push_back(v);
        }
    }

    void DFSArticulacao(int u, vector<bool> &visitado, vector<int> &disc, vector<int> &low, vector<int> &pai, vector<bool> &articulation_point, int &time) {
      /*essa função detecta pontos de articulação com base nas relações entre
      *os tempos de descoberta (disc) e os menores tempos acessiveis de cada vertice (low)
      */

        visitado[u] = true;
        disc[u] = low[u] = ++time; // Define o tempo de descoberta de u e inicializa low[u] com o mesmo valor
        int filho = 0;

        // Iteração sobre todas as arestas conectadas ao vértice u
        for (const auto &edge : adj_list[u]) {
            int v = edge[0]; // v é vértice adjacente a u

            if (!visitado[v]) {
                filho++;
                pai[v] = u; // define u como pai de v na árvore DFS
                DFSArticulacao(v, visitado, disc, low, pai, articulation_point, time); // se v não foi visitado, realiza a DFS em v

                low[u] = min(low[u], low[v]); // atualiza low[u] considerando a árvore DFS

                // Verifica se u é um ponto de articulação
                // Caso 1: Se u é a raiz e tem mais de um filho
                if (pai[u] == -1 && filho > 1) {
                    articulation_point[u] = true;
                }

                // Caso 2: Se u não é a raiz e low[v] >= disc[u], u é um ponto de articulação
                if (pai[u] != -1 && low[v] >= disc[u]) {
                    articulation_point[u] = true;
                }
            } else if (v != pai[u]) { // Se v já foi visitado e não é o pai de u, atualiza low[u]
                low[u] = min(low[u], disc[v]);
            }
        }
    }

    void DFSPontes(int u, vector<bool> &visitado, vector<int> &disc, vector<int> &low, vector<int> &pai, vector<pair<int, int>> &pontes, int &time) {
        visitado[u] = true;
        disc[u] = low[u] = ++time;

        // Itera sobre todas as arestas conectadas ao vértice u
        for (const auto &edge : adj_list[u]) {
            int v = edge[0];

            if (!visitado[v]) {
                pai[v] = u;
                DFSPontes(v, visitado, disc, low, pai, pontes, time);

                low[u] = min(low[u], low[v]);

                // Se low[v] > disc[u], (u, v) é uma ponte
                if (low[v] > disc[u]) {
                    pontes.push_back({u, v});
                }
            } else if (v != pai[u]) { // Se v já foi visitado e não é o pai de u, atualiza low[u]
                low[u] = min(low[u], disc[v]);
            }
        }
    }

    void encontrarVerticesArticulacao() { 
        vector<bool> visitado(vertices, false);
        vector<int> disc(vertices, -1); //armazena o tempo de descoberta
        vector<int> low(vertices, -1); //armazena o menor tempo de descoberta acessível a partir do vértice u
        vector<int> pai(vertices, -1); //armazena o pai de cada vertice
        vector<bool> articulation_point(vertices, false); //vetor booleano que indica se um vertice é ponto de articulação
        int time = 0; //rastreia o tempo de descoberta durante a dfs

        //dfs a partir de cada vertice não visitado
        for (int i = 0; i < vertices; i++) {
            if (!visitado[i]) {
                DFSArticulacao(i, visitado, disc, low, pai, articulation_point, time);
            }
        }

        vector<int> pontos_de_articulacao; //vetor que armazena os pontos de articulação encontrados
        for (int i = 0; i < vertices; i++) {
            if (articulation_point[i]) {
                pontos_de_articulacao.push_back(i);
            }
        }

        // Ordena os pontos de articulação em ordem crescente
        sort(pontos_de_articulacao.begin(), pontos_de_articulacao.end());

        int count = 0; //contador sobre o numero de pontos de articulação
    
        if (direcionado == true) { //apenas grafos não direcionados possuem pontos de articulação
            cout << "-1";
        } else {
            for (int v : pontos_de_articulacao) {
                cout << v << " ";
                count++;
            }
        } 
        if (count == 0 and direcionado == false){ //o grafo é não direcionado mas nenhum ponto de articulação foi encontrado
            cout << "-1";
        }
        cout << endl;
    }

    void encontrarArestasPonte () {
        vector<bool> visitado(vertices, false);
        vector<int> disc(vertices, -1);
        vector<int> low(vertices, -1);
        vector<int> pai(vertices, -1);
        vector<pair<int, int>> pontes; // Vetor para armazenar as pontes encontradas (pares de vértices)
        int time = 0; //rastreia o tempo de descoberta durante a dfs

        for (int i = 0; i < vertices; i++) {
            if (!visitado[i]) {
                DFSPontes(i, visitado, disc, low, pai, pontes, time);
            }
        }
        int count = 0; //contador para o número de arestas pontes

        if (direcionado == false) {
            for (const auto &bridge : pontes) {
                count++;
            }
        } else {
            cout << "-1" << endl;
        }
        if (direcionado == false) // Se o grafo não for direcionado, imprime o número de pontes encontradas
            cout << count << endl;
    }

    void DFS(int v, vector<bool> &visitado, stack<int> &Stack) {
        visitado[v] = true;
        for (const auto &edge : adj_list[v]) {
            int u = edge[0];
            if (!visitado[u]) {
                DFS(u, visitado, Stack);
            }
        }
        Stack.push(v); // empilha o vértice após visitar todos os seus adjacentes
    }

    void DFSTransposto(int v, vector<bool> &visitado) {
        visitado[v] = true;
        for (int u : adj_list_transposto[v]) {
            if (!visitado[u]) {
                DFSTransposto(u, visitado); // Realiza DFS recursivamente no grafo transposto
            }
        }
    }

    int encontrarComponentesFortementeConexos() {
      /*utiliza o algoritmo de Kosaraju para encontrar componentes fortemente conexos em um grafo direcionado*/
        stack<int> Stack;
        vector<bool> visitado(vertices, false);

        // Passo 1: Realizar DFS no grafo original e empilhar os vértices
        for (int i = 0; i < vertices; ++i) {
            if (!visitado[i]) {
                DFS(i, visitado, Stack);
            }
        }
        int count = 0;
        // Passo 2: Realizar DFS no grafo transposto
        fill(visitado.begin(), visitado.end(), false);
        while (!Stack.empty()) {
            int v = Stack.top();
            Stack.pop();

            if (!visitado[v]) {
                count++;
                DFSTransposto(v, visitado);
            }
        }

        if (direcionado == false){
            return -1;
        }

        return count;
    }

    void DFS(int v, vector<bool> &visitado) {
        visitado[v] = true;
        for (const auto &edge : adj_list[v]) {
            int u = edge[0]; // Obter o vértice de destino
            if (!visitado[u]) {
                DFS(u, visitado);
            }
        }
    }

    bool DFS(int v, vector<int> &estado, vector<bool> &rec_stack, bool detectar_ciclo) {
        if (detectar_ciclo) {
            estado[v] = 1; // Marca o vértice como visitado e em processamento
            rec_stack[v] = true; // Adiciona à pilha de recursão
        } else {
            estado[v] = 1; // Marca o vértice como visitado
        }

        for (const auto &edge : adj_list[v]) {
            int u = edge[0]; // Obter o vértice de destino
            
            if (detectar_ciclo) {
                if (rec_stack[u]) {
                    return true; // Encontrou um ciclo
                }
                if (estado[u] == 0) {
                    if (DFS(u, estado, rec_stack, detectar_ciclo)) {
                        return true; // Encontrou um ciclo em uma chamada recursiva
                    }
                }
            } else {
                if (estado[u] == 0) {
                    DFS(u, estado, rec_stack, detectar_ciclo); // Chama recursivamente DFS para o vértice adjacente
                }
            }
        }

        if (detectar_ciclo) {
            rec_stack[v] = false; // Remove da pilha de recursão
            estado[v] = 2; // Marca o vértice como totalmente visitado
        } else {
            estado[v] = 2; // Marca o vértice como totalmente visitado
        }

        return false; // Não encontrou ciclo
    }

    int verificarConexo() {
        vector<bool> visitado(vertices, false);
        DFS(0, visitado);
        for (int i = 0; i < vertices; ++i) {
            if (!visitado[i] && !adj_list[i].empty()) {
                return 0; // Não é conexo se algum vértice não for visitado e tiver arestas
            }
        }
        return 1;
    }

    bool verificarBipartido() {
        vector<int> cor(vertices, -1); // -1 indica que o vértice ainda não foi colorido
        queue<int> q;

        for (int i = 0; i < vertices; ++i) {
            if (cor[i] == -1) {
                cor[i] = 0;
                q.push(i);
                while (!q.empty()) {
                    int v = q.front();
                    q.pop();
                    for (const auto &edge : adj_list[v]) {
                        int u = edge[0]; // Obter o vértice de destino
                        if (cor[u] == -1) {
                            cor[u] = 1 - cor[v];
                            q.push(u);
                        } else if (cor[u] == cor[v]) {
                            return false; // O grafo não é bipartido
                        }
                    }
                }
            }
        }
        return true; // O grafo é bipartido
    }

    int verificarEuleriano() {
        if (!verificarConexo()) {
            return false; // O grafo deve ser conexo
        }

        //um grafo euleriano possui todos os vértices de grau par
        int num_impares = 0;
        for (int i = 0; i < vertices; ++i) {
            if (adj_list[i].size() % 2 != 0) {
                num_impares++;
            }
        }

        if (num_impares == 0) {
            return 1; // Todos os vértices têm grau par, é um ciclo euleriano
        } else if (num_impares == 2) {
            return -1; // Exatamente dois vértices têm grau ímpar, é um caminho euleriano
        } else {
            return 0; // Nenhuma das condições é satisfeita
        }
    }

    bool verificarCiclo() {
        vector<int> estado(vertices, 0); // 0: não visitado, 1: visitado e em processamento, 2: finalizado
        vector<bool> rec_stack(vertices, false); // Pilha de recursão

        // Verifica ciclos para todos os vértices
        for (int i = 0; i < vertices; ++i) {
            if (estado[i] == 0) {
                if (DFS(i, estado, rec_stack, true)) {
                    return true; // Encontrou um ciclo
                }
            }
        }
        return false; // Não encontrou ciclo
    }

    int encontrarComponentesConexos() {
        vector<bool> visitado(vertices, false);
        int count = 0; //contador para o número de componentes conexas

        for (int v = 0; v < vertices; ++v) {
            // Se o vértice v não foi visitado, é o início de um novo componente conexo
            if (!visitado[v]) {
                ++count;
                DFS(v, visitado);
            }
        }

        if (direcionado == true){ //o conceito de componentes conxeas é apenas para grafos não direcionados
            return -1;
        }

        return count;
    }

    void DFSArvore(int v, vector<bool> &visitado) {
        visitado[v] = true;

        // Ordena os vizinhos de acordo com a ordem lexicográfica dos vértices
        sort(adj_list[v].begin(), adj_list[v].end());

        for (const auto &edge : adj_list[v]) {
            int u = edge[0]; // Obtém o vértice adjacente u
            int id_aresta = edge[2];
            if (!visitado[u]) {
                cout << id_aresta << " ";
                DFSArvore(u, visitado);
            }
        }
    }

    void imprimirArvoreProfundidade() {
        vector<bool> visitado(vertices, false);

        // Inicia a DFS a partir da raiz 0
        DFSArvore(0, visitado);
        cout << endl;
    }

    void imprimirArvoreLargura() {
        vector<bool> visitado(vertices, false);
        queue<int> q; //fila para a bsf

        // Começa a BFS a partir do vértice 0
        visitado[0] = true;
        q.push(0);

        while (!q.empty()) {
            int v = q.front();
            q.pop();

            // Ordena os vizinhos de acordo com a ordem lexicográfica dos vértices
            sort(adj_list[v].begin(), adj_list[v].end());

            for (const auto &edge : adj_list[v]) {
                int u = edge[0];
                int id_aresta = edge[2];
                if (!visitado[u]) {
                    cout << id_aresta << " ";
                    visitado[u] = true;
                    q.push(u);
                }
            }
        }
        cout << endl;
    }

    int kruskall() {
        // Ordena as arestas com base no peso
        sort(arestas.begin(), arestas.end());

        int resultado = 0; //custo total da AGM
        UFDS ufds(vertices); // Cria a estrutura Union-Find para o número de vértices

        if (direcionado == true) //kruskall é para grafos não direcionados
            return -1;

        int numero_arestas = 0;
        for (auto &e : arestas) {
            int u = e.second.first;
            int v = e.second.second;
            if (!ufds.mesmoConjunto(u, v)) {
                resultado += e.first; // Adiciona o peso da aresta ao custo total
                numero_arestas++; // Incrementa o contador de arestas
                if (numero_arestas == vertices - 1) //kruskall é executado até ter n - 1 vértices
                    break;
                ufds.unionSet(u, v); // Une os conjuntos dos vértices u e v
            }
        }

        return resultado; //retorna o custo total da agm
    }

    void ordenacaoTopologica(int v, vector<bool> &visitado, stack<int> &Stack) {
            visitado[v] = true;

            // Ordena os vizinhos de acordo com a ordem lexicográfica dos vértices
            vector<int> vizinhos;
            for (const auto &edge : adj_list[v]) {
                vizinhos.push_back(edge[0]);
            }
            sort(vizinhos.begin(), vizinhos.end()); //lista dos vizinhos de v ordenados

            for (int u : vizinhos) {
                if (!visitado[u]) {
                    DFS(u, visitado, Stack);
                }
            }
            Stack.push(v); // Empilha o vértice v após visitar todos os vizinhos
    }

    void imprimirOrdenacaoTopologica() {
        if (direcionado == false) { // o grafo deve ser dirigido
            cout << "-1" << endl;
            return;
        }

        stack<int> Stack;
        vector<bool> visitado(vertices, false);

        // Realiza DFS para todos os vértices
        for (int i = 0; i < vertices; ++i) {
            if (!visitado[i]) {
                ordenacaoTopologica(i, visitado, Stack);
            }
        }

        // Imprime a ordenação topológica
        while (!Stack.empty()) {
            cout << Stack.top() << " ";
            Stack.pop();
        }
        cout << endl;
    }

    bool haPeloMenosDoisPesosDiferentes() {
        set<int> pesos;
        for (const auto &lista : adj_list) {
            for (const auto &aresta : lista) {
                pesos.insert(aresta[1]); // Adiciona o peso ao conjunto
                if (pesos.size() > 1) {
                    return true; // Já há pelo menos dois pesos diferentes
                }
            }
        }
        return false; // Todos os pesos são iguais ou não há arestas
    }

    int encontrarCaminhoMinimo() { //Dijkstra
        if (!haPeloMenosDoisPesosDiferentes()) {
            return -1;
        }

        // Usando Dijkstra para encontrar o caminho mínimo entre 0 e n-1
        vector<int> dist(vertices, numeric_limits<int>::max());
        priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> minHeap; // (distância, vértice)
        //fila de prioridade para encontrar o caminho mais curto

        dist[0] = 0; // Distância do vértice 0 para ele mesmo é 0
        minHeap.push({0, 0}); // (distância, vértice) inicializando com o vértice 0

        while (!minHeap.empty()) {
            // Obtém o vértice com a menor distância da fila
            int u = minHeap.top().second;
            int d = minHeap.top().first;
            minHeap.pop();

            if (d > dist[u]) {
                continue; // Ignorar se já encontramos um caminho melhor
            }

            for (const auto &edge : adj_list[u]) {
                int v = edge[0];
                int peso = edge[1];

                // Se a distância do vértice u mais o peso da aresta for menor do que a distância conhecida para o vértice v
                if (dist[u] + peso < dist[v]) {
                    dist[v] = dist[u] + peso;
                    minHeap.push({dist[v], v});
                }
            }
        }

        // Se a distância do vértice n-1 for infinita, significa que não há caminho para o vértice n-1, então retorna -1.
        // Caso contrário, retorna a distância do vértice 0 ao vértice n-1.
        return dist[vertices - 1] == numeric_limits<int>::max() ? -1 : dist[vertices - 1];
    }

    bool BFS(const vector<vector<int>> &residualGraph, vector<int> &pai) {
        fill(pai.begin(), pai.end(), -1); // Inicializa o vetor de pais com -1, indicando que os vértices ainda não foram visitados
        queue<int> q; //fila para realizar a bfs
        q.push(0); // Inicia a busca a partir do vértice 0
        pai[0] = -1;

        while (!q.empty()) {
            int u = q.front();
            q.pop();

            for (int v = 0; v < vertices; ++v) {
                if (pai[v] == -1 && residualGraph[u][v] > 0) { // Se o vértice v não foi visitado e há capacidade residual
                    q.push(v);
                    pai[v] = u;
                    if (v == vertices - 1) {
                        return true; // Se chegamos ao vértice destino
                    }
                }
            }
        }
        return false; // Não há caminho aumentante
    }

    int BFS(int s, int t, vector<int>& pai) {
        vector<bool> visitado(vertices, false);
        queue<int> q; //fila para realizar a bfs
        q.push(s);
        visitado[s] = true;
        pai[s] = -1;

        while (!q.empty()) {
            int u = q.front();
            q.pop();

            for (const auto& edge : adj_list[u]) {
                int v = edge[0];
                int capacidade = edge[1]; // Peso usado como capacidade

                if (!visitado[v] && capacidade > 0) { // Se o vértice não foi visitado e a capacidade é positiva
                    q.push(v);
                    pai[v] = u;
                    visitado[v] = true;
                    if (v == t) {
                        return true; // Se o destino é alcançado
                    }
                }
            }
        }
        return false;
    }
   
    int encontrarFluxoMaximo() { // Ford-Fulkerson
        if (direcionado == false){
            return -1;
        }

        int s = 0; // Origem
        int t = vertices - 1; // Destino
        int fluxo_maximo = 0;

        vector<int> pai(vertices); // Armazena o caminho

        while (BFS(s, t, pai)) {
            // Encontra o fluxo máximo que pode ser enviado pelo caminho encontrado
            int caminho_fluxo = numeric_limits<int>::max();
            for (int v = t; v != s; v = pai[v]) {
                int u = pai[v];
                for (auto& edge : adj_list[u]) {
                    if (edge[0] == v) {
                        caminho_fluxo = min(caminho_fluxo, edge[1]); // Peso como capacidade
                        break;
                    }
                }
            }

            // Atualiza capacidades residuais e fluxo máximo
            for (int v = t; v != s; v = pai[v]) {
                int u = pai[v];
                for (auto& edge : adj_list[u]) {
                    if (edge[0] == v) {
                        edge[1] -= caminho_fluxo; //// Subtrai o fluxo do caminho da capacidade residual
                        break;
                    }
                }
                // Adiciona a aresta reversa se não existir
                bool encontrado = false;
                for (auto& edge : adj_list[v]) {
                    if (edge[0] == u) {
                        edge[1] += caminho_fluxo; // Adiciona o fluxo reverso
                        encontrado = true;
                        break;
                    }
                }
                if (!encontrado) {
                    adj_list[v].push_back({u, caminho_fluxo, 0}); // Adiciona aresta reversa
                }
            }
            fluxo_maximo += caminho_fluxo;
        }

        return fluxo_maximo;
    }

    void DFSFecho(int v, vector<bool> &visitado) {
        visitado[v] = true;
        for (const auto &edge : adj_list[v]) {
            int u = edge[0];
            if (!visitado[u]) {
                DFS(u, visitado);
            }
        }
    }

    void fechoTransitivo() { //usa a dfsFecho e imprime todos os vertices que podem ser alcançados a partir do vertice 0
        vector<bool> visitado(vertices, false);

        // Realizar DFS a partir do vértice 0
        DFSFecho(0, visitado);

        vector<int> alcancaveis;
        for (int i = 1; i < vertices; ++i) {
            if (visitado[i]) {
                alcancaveis.push_back(i);
            }
        }

        if (alcancaveis.empty() or direcionado == false) {
            cout << "-1" << endl;
        } else {
            sort(alcancaveis.begin(), alcancaveis.end());
            for (int v : alcancaveis) {
                cout << v << " ";
            }
            cout << endl;
        }
    }

    void calcularGraus() {
        vector<int> grauEntrada(vertices, 0);
        vector<int> grauSaida(vertices, 0);

        // Calcular o grau de saída para cada vértice
        for (int u = 0; u < vertices; ++u) {
            grauSaida[u] = adj_list[u].size(); // Grau de saída é o número de arestas saindo de u
        }

        // Calcular o grau de entrada para cada vértice
        for (int u = 0; u < vertices; ++u) {
            for (const auto& aresta : adj_list[u]) {
                int v = aresta[0]; // Vértice de destino
                grauEntrada[v]++; // Incrementa o grau de entrada para o vértice de destino
            }
        }

        // Exibir os graus de entrada e saída
        cout << "Grau de saída:" << endl;
        for (int i = 0; i < vertices; ++i) {
            cout << "Vértice " << i << ": " << grauSaida[i] << endl;
        }

        cout << "Grau de entrada:" << endl;
        for (int i = 0; i < vertices; ++i) {
            cout << "Vértice " << i << ": " << grauEntrada[i] << endl;
        }
    }

    void trilhaEuleriana(int u, stack<int>& trilha) {
        while (!adj_list[u].empty()) {
        // Encontrar o próximo vértice
        auto& edge = adj_list[u].back();
        int v = edge[0];  // Vértice de destino

        // Remover a aresta v-u
        auto it = find_if(adj_list[v].begin(), adj_list[v].end(),
            [u, edge_id = edge[2]](const vector<int>& e) {
                return e[0] == u && e[2] == edge_id;
            });
        if (it != adj_list[v].end()) {
            adj_list[v].erase(it);
        }

        // Remover a aresta u-v
        adj_list[u].pop_back();

        // Recursivamente continuar com o próximo vértice
        trilhaEuleriana(v, trilha);
        }
        // Adicionar o vértice ao caminho euleriano
        trilha.push(u);
    }

    void imprimirTrilhaEuleriana() {
      if (verificarEuleriano() == -1 or verificarEuleriano() == 1){ 

        // Encontrar um vértice com grau ímpar para iniciar (ou qualquer vértice se todos forem pares)
        int inicio = 0;
        for (int i = 0; i < vertices; ++i) {
            if (adj_list[i].size() % 2 != 0) {
                inicio = i;
                break;
            }
        }

        stack<int> trilha;
        trilhaEuleriana(inicio, trilha);

        // Imprimir a trilha euleriana
        cout << "Trilha Euleriana: ";
        while (!trilha.empty()) {
            cout << trilha.top() << " ";
            trilha.pop();
        }
        cout << endl;
      }
    }

    void imprimirAdjList() const {
            for (int u = 0; u < vertices; ++u) {
                cout << "Vértice " << u << ": ";
                for (const auto& aresta : adj_list[u]) {
                    cout << "-> (Vértice: " << aresta[0]
                            << ", Peso: " << aresta[1]
                            << ", ID Aresta: " << aresta[2] << ") ";
                }
                cout << endl;
            }
        }

};

Grafo lerGrafo() {
    int vertices;
    cin >> vertices;

    int arestas;
    cin >> arestas;

    string tipo_grafo;
    cin >> tipo_grafo;
    bool direcionado = (tipo_grafo == "direcionado");

    Grafo grafo(vertices, direcionado);

    for (int i = 0; i < arestas; i++) {
        int id_aresta, u, v, peso;
        cin >> id_aresta >> u >> v >> peso;
        grafo.adicionarAresta(id_aresta, u, v, peso);
    }

    return grafo;
}

int main() {

    Grafo grafo;

    cout << "MENU" << endl;
    cout << "----------Verificar----------\n";
    cout << "1. Conexo\n";
    cout << "2. Bipartido\n";
    cout << "3. Euleriano\n";
    cout << "4. Cíclico\n";
    cout << "----------Listar----------\n";
    cout << "5. Componentes conexas\n";
    cout << "6. Componentes fortemente conexas\n";
    cout << "7. Vértices de articulação\n";
    cout << "8. Arestas ponte\n";
    cout << "----------Gerar----------\n";
    cout << "9. Árvore de profundidade\n";
    cout << "10. Árvore de largura\n";
    cout << "11. Árvore geradora mínima\n";
    cout << "12. Ordem topológica (Disponível apenas para grafos direcionados)\n";
    cout << "13. Caminho mínimo entre dois vértices (Disponível apenas para grafos ponderados)\n";
    cout << "14. Fluxo máximo (Disponível apenas para grafos ponderados)\n";
    cout << "15. Fecho transitivo (Disponível apenas para grafos ponderados)\n";
    cout << "----------EXTRAS----------\n";
    cout << "16. Gerar trilha euleriana para grafos não orientados\n";
    cout << "17. Mostrar grau de entrada e saída de um grafo orientado\n";
    cout << "18. Imprimir a lista de adjacência do grafo\n\n";
    cout << "Digite as opçoes: " << endl;

    string linha;
    vector<int> comandos;

    // Lê a primeira linha de entrada
    getline(cin, linha);

    // Usa uma stringstream para dividir a linha em inteiros
    stringstream ss(linha);
    int comando;
    while (ss >> comando) {
        comandos.push_back(comando);
    }

    cout << "Digite o grafo a ser analisado: " << endl;
    grafo = lerGrafo();

    int conexo = grafo.verificarConexo();
    int bipartido = grafo.verificarBipartido();
    int euleriano = grafo.verificarEuleriano();
    int ciclo = grafo.verificarCiclo();
    int componenteConexo = grafo.encontrarComponentesConexos();
    int fortementeConexo = grafo.encontrarComponentesFortementeConexos();
    int agm = grafo.kruskall();
    int caminhoMinimo = grafo.encontrarCaminhoMinimo();
    int fluxoMaximo = grafo.encontrarFluxoMaximo();

    for (int c : comandos) {
    switch (c) {
        case 0:
            cout << conexo << endl;
            break;
        case 1:
            cout << bipartido << endl;
            break;
        case 2:
            cout << euleriano << endl;
            break;
        case 3:
            cout << ciclo << endl;
            break;
        case 4:
            cout << componenteConexo << endl;
            break;
        case 5:
            cout << fortementeConexo << endl;
            break;
        case 6:
            grafo.encontrarVerticesArticulacao();
            break;
        case 7:
            grafo.encontrarArestasPonte();
            break;
        case 8:
            grafo.imprimirArvoreProfundidade();
            break;
        case 9:
            grafo.imprimirArvoreLargura();
            break;
        case 10:
            cout << agm << endl;
            break;
        case 11:
            grafo.imprimirOrdenacaoTopologica();
            break;
        case 12:
            cout << caminhoMinimo << endl;;
            break;
        case 13:
            cout << fluxoMaximo << endl;
            break;
        case 14:
            grafo.fechoTransitivo();
            break;
        case 15:
            grafo.imprimirTrilhaEuleriana();
            break;
        case 16:
            grafo.calcularGraus();
            break;
        case 17:
            grafo.imprimirAdjList();
            break;
        default:
            cout << "Comando inválido\n";
    }
}
    
    return 0;
}
