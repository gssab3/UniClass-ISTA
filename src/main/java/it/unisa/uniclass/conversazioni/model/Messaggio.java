package it.unisa.uniclass.conversazioni.model;

import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.persistence.*;

import java.io.Serializable;
import java.time.LocalDateTime;


/**
 * Rappresenta un messaggio scambiato tra utenti in una conversazione.
 * E' persistito in un database tramite JPA.
 * */
@Entity
@Access(AccessType.FIELD)
@Table(name = "messaggi")
@NamedQueries({
        @NamedQuery(name = "Messaggio.trovaMessaggio", query = "SELECT m FROM Messaggio m WHERE m.id = :id"),
        @NamedQuery(name = "Messaggio.trovaMessaggiInviati", query = "SELECT m FROM Messaggio m WHERE m.autore.matricola = :matricola"),
        @NamedQuery(name = "Messaggio.trovaMessaggiRicevuti", query = "SELECT m FROM Messaggio m WHERE m.destinatario.matricola = :matricola"),
        @NamedQuery(name = "Messaggio.trovaMessaggiMessaggeri", query = "SELECT m FROM Messaggio m WHERE ((m.autore.matricola = :autore) AND (m.destinatario.matricola = :destinatario)) OR ((m.autore.matricola = :destinatario) AND (m.destinatario.matricola = :autore))"),
        @NamedQuery(name = "Messaggio.trovaTutti", query = "SELECT m FROM Messaggio m"),
        @NamedQuery(name = "Messaggio.trovaAvvisi", query = "SELECT m FROM Messaggio m WHERE m.topic <> null"),
        @NamedQuery(name = "Messaggio.trovaAvvisiAutore", query = "SELECT m FROM Messaggio m WHERE m.topic <> null AND m.autore.matricola = :autore"),
        @NamedQuery(name = "Messaggio.trovaMessaggiData", query = "SELECT m FROM Messaggio m WHERE m.dateTime = :dateTime"),
        @NamedQuery(name = "Messaggio.trovaTopic", query = "SELECT m FROM Messaggio m WHERE m.topic = :topic")
})
public class Messaggio implements Serializable {

    /**
     * Nome della query per trovare un messaggio tramite ID
     * */
    public static final String TROVA_MESSAGGIO = "Messaggio.trovaMessaggio";
    /**
     * Nome della query per trovare i messaggi inviati da un autore.
     * */
    public static final String TROVA_MESSAGGI_INVIATI = "Messaggio.trovaMessaggiInviati";

    /**
     * Nome della query per trovare i messaggi ricevuti da un accademico
     */
    public static final String TROVA_MESSAGGI_RICEVUTI = "Messaggio.trovaMessaggiRicevuti";

    /**
     * Nome della query per trovare i messaggi tra due specifici utenti.
     * */
    public static final String TROVA_MESSAGGI_MESSAGGERI = "Messaggio.trovaMessaggiMessaggeri";
    /**
     * Nome della query per trovare tutti i messsaggi.
     * */
    public static final String TROVA_TUTTI = "Messaggio.trovaTutti";
    /**
     * Nome della query per trovare tutti gli avvisi.
     * */
    public static final String TROVA_AVVISI = "Messaggio.trovaAvvisi";
    /**
     * Nome della query per trovare gli avvisi creati da un autore specifico.
     * */
    public static final String TROVA_AVVISI_AUTORE = "Messaggio.trovaAvvisiAutore";
    /**
     * Nome della query per trovare i messaggi in base alla data e ora.
     * */
    public static final String TROVA_MESSAGGI_DATA = "Messaggio.trovaMessaggiData";
    /**
     * Nome della query per trovare i messaggi in base all'id del topic (eventuale)
     */
    public static final String TROVA_TOPIC = "Messaggio.trovaTopic";

    @Id @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;

    /**
     * Data e ora di creazione del messaggio.
     * Il valore di default viene impostato automaticamente tramite il metodo prePersist.
     */
    @Column(name = "data_time", nullable = false)
    private LocalDateTime dateTime;

    /**
     * Testo del messaggio, ovvero il contenuto del messaggio stesso.
     * E' un campo obbligatorio.
     */
    @Column(name = "body", nullable = false, columnDefinition = "TEXT")
    private String body;

    /**
     * Autore del messaggio. E' un riferimento a un oggetto di tipo Accademico.
     * */
    @ManyToOne
    @JoinColumn(name = "autore")
    //@ spec_public
    //@ nullable
    private Accademico autore;

    /**
     * Destinatario del messaggio. E' un riferimento a un oggetto di tipo Accademico.
     * */
    @ManyToOne
    @JoinColumn(name = "destinatario")
    //@ spec_public
    //@ nullable
    private Accademico destinatario;

    /**
     * Topic del messaggio eventuale.
     */

    @ManyToOne(cascade = CascadeType.PERSIST)
    @JoinColumn(name = "topic")
    //@ spec_public
    //@ nullable
    private Topic topic;

    //Getter e Setter con Javadoc
    /**
     * Restituisce il destinatario del messaggio.
     *
     * @return Il destinatario
     * */
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == destinatario;
      @*/
    public /*@ nullable */ Accademico getDestinatario() {
        return destinatario;
    }

    /**
     * Imposta il destinatario del messaggio
     *
     * @param destinatario Il destinatario da impostare.
     * */
    public void setDestinatario(Accademico destinatario) {
        this.destinatario = destinatario;
    }

    /**
     * Restituisce l'autore del messaggio.
     *
     * @return L'autore.
     * */
    public Accademico getAutore() {
        return autore;
    }

    /**
     * Imposta l'autore del messaggio
     *
     * @param autore L'autore da impostare.
     * */
    public void setAutore(Accademico autore) {
        this.autore = autore;
    }

    /**
     * Costruttore vuoto necessario per JPA.
     */
    public Messaggio() {}

    /**
     * Metodo chiamato automaticamente prima del persist.
     * Imposta la data e ora corrente se non è già stata impostata.
     */
    @PrePersist
    protected void onCreate() {
        if (this.dateTime == null) {
            this.dateTime = LocalDateTime.now();
        }
    }

    /**
     * Costruttore per inizializzare un messaggio con i dati principali.
     *
     * @param autore    L'autore del messaggio
     * @param destinatario  Il destinatario del messaggio
     * @param topic Il topic del messaggio (opzionale)
     * @param body  Il testo del messaggio
     * @param dateTime  La data e ora di creazione
     */
    public Messaggio(Accademico autore, Accademico destinatario, Topic topic, String body, LocalDateTime dateTime) {
        this.autore = autore;
        this.destinatario = destinatario;
        this.topic = topic;
        this.body = body;
        this.dateTime = dateTime;
    }


    /**
     * Restituisce la data e ora di creazione del messaggio.
     *
     * @return La data e ora.
     *
     * */
    public LocalDateTime getDateTime() {
        return dateTime;
    }

    /**
     * Imposta la data e ora di creazione del messaggio.
     *
     * @param dateTime La data e ora da impostare.
     * */
    public void setDateTime(LocalDateTime dateTime) {
        this.dateTime = dateTime;
    }

    /**
     * Restituisce il testo del messaggio.
     *
     * @return Il testo.
     */
    public String getBody() {
        return body;
    }

    /**
     * Imposta il testo del messaggio.
     *
     * @param body Il testo da impostare.
     */
    public void setBody(String body) {
        this.body = body;
    }

    /**
     * Restituisce il topic del messaggio.
     *
     * @return Il topic.
     * */
    public /*@ nullable */ Topic getTopic() {
        return topic;
    }

    /**
     * Imposta il topic del messaggio.
     *
     * @param topic Il topic da impostare.
     * */
    public void setTopic(Topic topic) {
        this.topic = topic;
    }

    /**
     * Restituisce l'id del messaggio
     *
     * @return L'id
     */
    public Long getId() {
        return id;
    }

    /**
     * Rappresentazione testuale dell'oggetto Messaggio.
     *
     * @return Una stringa che descrive il messaggio.
     * */
    @Override
    public String toString() {
        return "Messaggio{" +
                "id=" + id +
                ", topic='" + topic + '\'' +
                ", dateTime=" + dateTime +
                ", body='" + body + '\'' +
                ", autore=" + autore +
                ", destinatario=" + destinatario +
                '}';
    }
}
