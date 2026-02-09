package it.unisa.uniclass.orari.model;

import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.persistence.*;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

/**
 * Classe rappresentante un "Resto", che identifica una suddivisione di studenti all'interno di un corso di laurea.
 * Viene mappata come entità JPA per la persistenza.
 * */
@Entity
@Access(AccessType.FIELD)
@NamedQueries({
        @NamedQuery(name = "Resto.trovaRestiCorso", query = "SELECT r FROM Resto r WHERE r.corsoLaurea.nome = :nome"),
        @NamedQuery(name = "Resto.trovaResto", query = "SELECT r FROM Resto r WHERE r.id = :id"),
        @NamedQuery(name = "Resto.trovaRestoNome", query = "SELECT r FROM Resto r WHERE r.nome = :nome"),
        @NamedQuery(name = "Resto.trovaRestoNomeCorso", query = "SELECT r FROM Resto r JOIN r.corsoLaurea cl WHERE r.nome = :nome AND cl.nome = :nomeCorso")
})
public class Resto implements Serializable {

    /**
     * Nome della query per trovare i "Resto" associati a un corso di laurea.
     * */
    public static final String TROVA_RESTI_CORSO = "Resto.trovaRestiCorso";
    /**
     * Nome della query per trovare un singolo "Resto" tramite il suo ID.
     * */
    public static final String TROVA_RESTO = "Resto.trovaResto";
    /**
     * Nome della query per trovare un "Resto" tramite il nome.
     * */
    public static final String TROVA_RESTO_NOME = "Resto.trovaRestoNome";
    /**
     * Nome della query per trovare un "Resto" tramite il nome e il nome del corso di laurea.
     * */
    public static final String TROVA_RESTO_NOME_CORSO = "Resto.trovaRestoNomeCorso";

    /**
     * ID univoco del resto/sezione.
     */
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;

    /**
     * Nome del resto/sezione.
     */
    private String nome; // Esempio: "Resto 0", "Resto 1", ecc.

    /**
     * Elenco delle lezioni associate a questo resto.
     */
    @OneToMany(mappedBy = "resto", cascade = CascadeType.ALL, fetch = FetchType.EAGER)
    private List<Lezione> lezioni = new ArrayList<>();

    /**
     * Corso di laurea a cui appartiene questo resto.
     */
    @ManyToOne
    @JoinColumn(name = "corso_laurea_id", nullable = false)
    private CorsoLaurea corsoLaurea;

    /**
     * Elenco degli studenti associati a questo resto.
     */
    @OneToMany(mappedBy = "resto", cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    private List<Accademico> accademici = new ArrayList<>();


    /**
     * Costruttore che inizializza un nuovo oggetto Resto con il nome e il corso di laurea associato.
     *
     * @param nome Nome del resto (esempio: "Resto 1").
     * @param corsoLaurea Corso di laurea a cui appartiene il resto.
     * */
    public Resto(String nome, CorsoLaurea corsoLaurea) {
        this.nome = nome;
        this.corsoLaurea = corsoLaurea;
    }

    /**
     * Costruttore vuoto richiesto per il funzionamento con JPA.
     * */
    public Resto() {
    }

    public void setId(Long id) {this.id = id;}
    public Long getId() {return id;}

    public String getNome() {return nome;}
    public void setNome(String nome) {this.nome = nome;}


    public CorsoLaurea getCorsoLaurea() {return corsoLaurea;}
    public void setCorsoLaurea(CorsoLaurea corsoLaurea) {this.corsoLaurea = corsoLaurea;}

    public List<Lezione> getLezioni() {return lezioni;}
    public void setLezioni(List<Lezione> lezioni) {this.lezioni = lezioni;}

    public List<Accademico> getAccademici() {return accademici;}
    public void setAccademici(List<Accademico> accademici) {this.accademici = accademici;}
}
