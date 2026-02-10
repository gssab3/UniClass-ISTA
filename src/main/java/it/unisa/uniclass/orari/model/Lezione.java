package it.unisa.uniclass.orari.model;

import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.persistence.*;

import java.io.Serializable;
import java.sql.Time;
import java.util.List;
import java.util.ArrayList;

/**
 * Rappresenta una lezione nel sistema di gestione orari.
 * Contiene informazioni come la data, l'orario, il giorno, il corso associato, l'aula e altre proprietà rilevanti.
 * */

@Entity
@Access(AccessType.FIELD)
@Table(name = "lezioni")
@NamedQueries({
        @NamedQuery(name = "Lezione.trovaLezione", query = "SELECT l FROM Lezione l WHERE l.id = :id"),
        @NamedQuery(name = "Lezione.trovaLezioneCorso", query = "SELECT l FROM Lezione l WHERE l.corso.nome = :nomeCorso"),
        @NamedQuery(name = "Lezione.trovaLezioneOre", query = "SELECT l FROM Lezione l WHERE l.oraInizio = :oraInizio AND l.oraFine = :oraFine"),
        @NamedQuery(name = "Lezione.trovaLezioneOreGiorno", query = "SELECT l FROM Lezione l WHERE l.giorno = :giorno AND l.oraInizio = :oraInizio AND l.oraFine = :oraFine"),
        @NamedQuery(name = "Lezione.trovaLezioneAula", query = "SELECT l FROM Lezione l WHERE l.aula.nome = :nome"),
        @NamedQuery(name = "Lezione.trovaTutte", query = "SELECT l FROM Lezione l"),
        @NamedQuery(name = "Lezione.trovaLezioneCorsoRestoAnno",
                query = "SELECT l FROM Lezione l " +
                        "JOIN l.corso c " +
                        "JOIN c.corsoLaurea cl " +
                        "JOIN l.resto r " +
                        "JOIN c.annoDidattico a " +
                        "WHERE cl.id = :corsoLaureaId " +
                        "AND r.id = :restoId " +
                        "AND a.id = :annoId"),
        @NamedQuery(name = "Lezione.trovaLezioneCorsoRestoAnnoSemestre", query = "SELECT l FROM Lezione l " +
                "JOIN l.corso c " +
                "JOIN c.corsoLaurea cl " +
                "JOIN l.resto r " +
                "JOIN c.annoDidattico a " +
                "WHERE cl.id = :corsoLaureaId " +
                "AND r.id = :restoId " +
                "AND a.id = :annoId AND l.semestre = :semestre"),

        @NamedQuery(name = "Lezione.trovaLezioniDocente", query = "SELECT l FROM Lezione l JOIN l.accademici a WHERE a.nome = :nomeDocente")})

public class Lezione implements Serializable {

    /**
     * Query per trovare una lezione tramite ID
     * */
    public final static String TROVA_LEZIONE = "Lezione.trovaLezione";
    /**
     * Query per trovare lezioni associate a un corso specifico.
     * */
    public final static String TROVA_LEZIONE_CORSO = "Lezione.trovaLezioneCorso";
    /**
     * Query per trovare lezioni in base all'orario di inizio e fine.
     * */
    public final static String TROVA_LEZIONE_ORE = "Lezione.trovaLezioneOre";
    /**
     * Query per trovare lezioni in base all'orario e al giorno
     * */
    public final static String TROVA_LEZIONE_ORE_GIORNO = "Lezione.trovaLezioneOreGiorno";
    /**
     * Query per trovare lezioni in base all'aula
     * */
    public static final String TROVA_LEZIONE_AULA = "Lezione.trovaLezioneAula";
    /**
     * Query per trovare tutte le lezioni.
     * */
    public static final String TROVA_TUTTE = "Lezione.trovaTutte";
    /**
     * Query per trovare lezioni in base al corso, resto e anno.
     * */
    public static final String TROVA_LEZIONE_CORSO_RESTO_ANNO = "Lezione.trovaLezioneCorsoRestoAnno";
    /**
     * Query per trovare lezioni in base al corso, resto, anno e semestre.
     * */
    public static final String TROVA_LEZIONE_CORSO_RESTO_ANNO_SEMESTRE = "Lezione.trovaLezioneCorsoRestoAnnoSemestre";
    /**
     * Query per trovare lezioni di uno specifico docente.
     * */
    public static final String TROVA_LEZIONI_DOCENTE = "Lezione.trovaLezioniDocente";

    /**
     * Identificativo univoco per Lezione
     */
    @Id @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;

    /**
     * Lista dei docenti che presenziano la lezione
     */
    @ManyToMany(mappedBy = "lezioni")
    private List<Accademico> accademici = new ArrayList<>();

    /**
     * Semestre in cui è presente la lezione
     */
    private int semestre; //1 o 2

    /**
     * Ora di Inizio della Lezione
     */
    private Time oraInizio;

    /**
     * Ora di Fine della lezione
     */
    private Time oraFine;

    /**
     * Giorno della settimana in cui si sostiene la lezione (Tramite Enumeratore)
     */
    @Enumerated(EnumType.STRING)
    private Giorno giorno;

    /**
     * Corso della lezione
     */
    @ManyToOne
    @JoinColumn(name = "corso_id")
    private Corso corso;

    /**
     * Resto o Sezione della classe che segue la lezione
     */
    @ManyToOne
    @JoinColumn(name = "resto_id")
    private Resto resto;

    /**
     * Aula in cui è presente la lezione
     */
    @ManyToOne(cascade = CascadeType.PERSIST)
    @JoinColumn(name = "aula_id")
    private Aula aula;

    // --- Costruttori ---

    /**
     *
     * Costruttore predefinito.
     * */
    public Lezione() {}

    /**
     * Costruttore con parametri.
     *
     * @param oraInizio L'orario di inizio.
     * @param semestre Il semestre considerato.
     * @param oraFine L'orario di fine.
     * @param giorno Il giorno della settimana,.
     * @param resto Informazioni aggiuntive sulla lezione.
     * @param corso Il corso associato.
     * @param aula L'aula della lezione
     * */
    public Lezione(int semestre, Time oraInizio, Time oraFine, Giorno giorno, Resto resto, Corso corso, Aula aula) {
        this.oraInizio = oraInizio;
        this.semestre = semestre;
        this.oraFine = oraFine;
        this.giorno = giorno;
        this.resto = resto;
        this.corso = corso;
        this.aula = aula;
    }

    // --- Getters e Setters ---


    public List<Accademico> getAccademici() {
        return accademici;
    }
    public void setAccademici(List<Accademico> accademici) {
        this.accademici = accademici;
    }

    public int getSemestre() {
        return semestre;
    }
    public void setSemestre(int semestre) {
        this.semestre = semestre;
    }

    public Time getOraInizio() {
        return oraInizio;
    }
    public void setOraInizio(Time oraInizio) {
        this.oraInizio = oraInizio;
    }

    public Time getOraFine() {
        return oraFine;
    }
    public void setOraFine(Time oraFine) {
        this.oraFine = oraFine;
    }

    public Giorno getGiorno() {
        return giorno;
    }
    public void setGiorno(Giorno giorno) {
        this.giorno = giorno;
    }

    public Resto getResto() {
        return resto;
    }
    public void setResto(Resto resto) {
        this.resto = resto;
    }

    public Long getId() {
        return id;
    }

    public Corso getCorso() {return corso;}
    public void setCorso(Corso corso) {
        this.corso = corso;
    }


    public Aula getAula() {
        return aula;
    }
    public void setAula(Aula aula) {
        this.aula = aula;
    }



    @Override
    public String toString() {
        return "Lezione{" +
                "id=" + id +
                ", semestre=" + semestre +
                ", oraInizio=" + oraInizio +
                ", oraFine=" + oraFine +
                ", giorno=" + giorno +
                ", corso=" + corso +
                ", resto=" + resto +
                ", aula=" + aula +
                '}';
    }
}