package it.unisa.uniclass.orari.model;

import jakarta.persistence.*;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

/**
 * Classe rappresentante un "Resto", che identifica una suddivisione di studenti all'interno di un  corso di laurea.
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
    //@ spec_public
    //@ nullable
    private Long id;

    /**
     * Nome del resto/sezione.
     */
    //@ spec_public
    //@ nullable
    private String nome; // Esempio: "Resto 0", "Resto 1", ecc.

    /**
     * Elenco delle lezioni associate a questo resto.
     */
    @OneToMany(mappedBy = "resto", cascade = CascadeType.ALL, fetch = FetchType.EAGER)
    //@ spec_public
    //@ nullable
    private List<Lezione> lezioni = new ArrayList<>();

    /**
     * Corso di laurea a cui appartiene questo resto.
     */
    @ManyToOne
    @JoinColumn(name = "corso_laurea_id", nullable = false)
    //@ spec_public
    //@ nullable
    private CorsoLaurea corsoLaurea;

    /**
     * Elenco degli studenti associati a questo resto.
     */
    @OneToMany(mappedBy = "resto", cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    //@ spec_public
    //@ nullable
    private List<Studente> studenti = new ArrayList<>();


    /**
     * Costruttore che inizializza un nuovo oggetto Resto con il nome e il corso di laurea associato.
     *
     * @param nome Nome del resto (esempio: "Resto 1").
     * @param corsoLaurea Corso di laurea a cui appartiene il resto.
     * */
    /*@
      @ public normal_behavior
      @ assignable \everything;
      @ ensures this.nome == nome;
      @ ensures this.corsoLaurea == corsoLaurea;
      @ ensures true;
      @*/
    public Resto(String nome, CorsoLaurea corsoLaurea) {
        this.nome = nome;
        this.corsoLaurea = corsoLaurea;
    }

    /**
     * Costruttore vuoto richiesto per il funzionamento con JPA.
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures true;
      @*/
    public Resto() {
    }

    /**
     * Restituisce l'ID del resto.
     *
     * @return ID univoco del resto.
     * */
    /*@
      @ public normal_behavior
      @ ensures \result == id;
      @*/
    public /*@ nullable */ Long getId() {
        return id;
    }

    /**
     * Restituisce il nome del resto.
     *
     * @return Nome del resto.
     * */
    /*@
      @ public normal_behavior
      @ ensures \result == nome;
      @*/
    public /*@ nullable */ String getNome() {
        return nome;
    }

    /**
     * Restituisce il corso di laurea associato a questo resto.
     *
     * @return Oggetto {@link CorsoLaurea} a cui appartiene il resto.
     * */
    /*@
      @ public normal_behavior
      @ ensures \result == corsoLaurea;
      @*/
    public /*@ nullable */ CorsoLaurea getCorsoLaurea() {
        return corsoLaurea;
    }

    /**
     * Imposta un nuovo nome per il resto
     *
     * @param nome Nuovo nome del resto.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.nome;
      @ ensures this.nome == nome;
      @*/
    public void setNome(String nome) {
        this.nome = nome;
    }

    /**
     * Imposta un nuovo corso di laurea associato al resto.
     *
     * @param corsoLaurea Nuovo corso di laurea.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.corsoLaurea;
      @ ensures this.corsoLaurea == corsoLaurea;
      @*/
    public void setCorsoLaurea(CorsoLaurea corsoLaurea) {
        this.corsoLaurea = corsoLaurea;
    }
}
